#!/usr/bin/env python3
"""
update_theorem_links.py

A tool to index declarations (theorems, definitions, lemmas, classes, structures,
and fields) across the Praxeology Lean 4 codebase and audit / update references
in Markdown documentation.

Features:
- Indexes all Lean declarations and structure fields with file paths and line numbers.
- Identifies outdated line numbers (`#L...`) in Markdown links.
- Identifies symbols that moved to a different Lean file.
- Automatic fix mode (`--fix`) to rewrite links in-place with up-to-date targets.
- CI check mode (`--check`) that exits with non-zero code on outdated links.
- Dry-run mode (`--dry-run`) to preview changes without modifying files.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from urllib.parse import unquote, urlsplit
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple


@dataclass
class LeanDeclaration:
    name: str
    file_path: Path
    line_number: int
    decl_type: str


class LeanIndexer:
    """Indexes declarations and structure fields across Lean source files."""

    DECL_PATTERN = re.compile(
        r"^(?:@\[[^\]]+\]\s*)*(?:(?:noncomputable|scoped|private|protected|omit)\s+)*"
        r"(def|theorem|lemma|class|structure|abbrev|inductive|instance)\s+"
        r"([A-Za-z0-9_\'\.]+)"
    )
    FIELD_PATTERN = re.compile(r"^\s{2,4}([A-Za-z0-9_\']+)\s*(?:\([^)]*\))?\s*:\s+")
    STRUCT_PATTERN = re.compile(r"^(?:(?:class|structure)\s+)([A-Za-z0-9_\']+)")

    def __init__(self, root_dir: Path):
        self.root_dir = root_dir.resolve()
        # Map: (file_rel_path, symbol_name) -> LeanDeclaration
        self.by_file_and_name: Dict[Tuple[str, str], LeanDeclaration] = {}
        # Map: symbol_name -> List[LeanDeclaration]
        self.by_name: Dict[str, List[LeanDeclaration]] = {}

    def index(self) -> None:
        lean_files = list(self.root_dir.glob("Praxeology/**/*.lean"))
        root_lean = self.root_dir / "Praxeology.lean"
        if root_lean.exists():
            lean_files.append(root_lean)

        for path in lean_files:
            rel_path = path.relative_to(self.root_dir).as_posix()
            file_name = path.name
            try:
                with open(path, "r", encoding="utf-8", errors="replace") as f:
                    lines = f.readlines()
            except OSError as e:
                print(f"[!] Warning: Could not read {path}: {e}", file=sys.stderr)
                continue

            in_struct = False
            for line_no, line in enumerate(lines, 1):
                # Check top-level / scoped declaration
                m_decl = self.DECL_PATTERN.match(line.strip())
                if m_decl:
                    decl_type, raw_name = m_decl.groups()
                    # Clean up qualified names (e.g. Praxeology.foo -> foo)
                    short_name = raw_name.split(".")[-1]
                    decl = LeanDeclaration(
                        name=short_name,
                        file_path=path,
                        line_number=line_no,
                        decl_type=decl_type,
                    )
                    self._register(rel_path, file_name, short_name, decl)
                    if raw_name != short_name:
                        self._register(rel_path, file_name, raw_name, decl)

                # Check structure / class field declaration
                m_field = self.FIELD_PATTERN.match(line)
                if m_field:
                    field_name = m_field.group(1)
                    key = (file_name, field_name)
                    if key not in self.by_file_and_name:
                        decl = LeanDeclaration(
                            name=field_name,
                            file_path=path,
                            line_number=line_no,
                            decl_type="field",
                        )
                        self._register(rel_path, file_name, field_name, decl)

    def _register(self, rel_path: str, file_name: str, name: str, decl: LeanDeclaration) -> None:
        self.by_file_and_name[(rel_path, name)] = decl
        self.by_file_and_name[(file_name, name)] = decl
        self.by_name.setdefault(name, []).append(decl)

    def find_declaration(self, symbol: str, target_file_hint: Optional[str] = None) -> Optional[LeanDeclaration]:
        candidates = self.find_declarations(symbol)
        if target_file_hint:
            hint = Path(target_file_hint).as_posix()
            matches = [d for d in candidates if d.file_path.resolve().as_posix().endswith(hint)]
            if len(matches) == 1:
                return matches[0]
        return candidates[0] if len(candidates) == 1 else None

    def find_declarations(self, symbol: str) -> List[LeanDeclaration]:
        """Return unique source declarations for a short or qualified name."""
        found = self.by_name.get(symbol, [])
        unique: Dict[Tuple[str, int], LeanDeclaration] = {}
        for decl in found:
            unique[(decl.file_path.resolve().as_posix(), decl.line_number)] = decl
        return list(unique.values())


@dataclass
class LinkIssue:
    file_path: Path
    line_number: int
    symbol: str
    old_link: str
    new_link: str
    reason: str


class MarkdownLinkAuditor:
    """Audits and fixes Lean codebase links in Markdown files."""

    # Matches Markdown links to .lean files: [text](target)
    # Group 1: text, Group 2: full url/path, Group 3: file path, Group 4: optional line #L123
    LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]*?\.lean(?:#L\d+)?[^)]*)\)")

    def __init__(self, indexer: LeanIndexer, root_dir: Path, add_missing: bool = False):
        self.indexer = indexer
        self.root_dir = root_dir.resolve()
        self.add_missing = add_missing

    def audit_file(self, md_path: Path) -> List[LinkIssue]:
        issues: List[LinkIssue] = []
        try:
            with open(md_path, "r", encoding="utf-8", errors="replace") as f:
                lines = f.readlines()
        except OSError as e:
            print(f"[!] Warning: Could not read {md_path}: {e}", file=sys.stderr)
            return issues

        for line_no, line in enumerate(lines, 1):
            for m in self.LINK_RE.finditer(line):
                link_text, full_url = m.groups()
                target = self._resolve_local_lean_path(md_path, full_url)
                if target is None:
                    continue
                old_link = m.group(0)
                symbol = self._extract_symbol(link_text, line)
                explicit = bool(re.search(r"`([A-Za-z0-9_\'\.]+)`", link_text))
                target_exists = target.exists()
                if symbol == target.stem and target_exists:
                    symbol = None
                    explicit = False

                if not target_exists and not symbol:
                    issues.append(LinkIssue(md_path, line_no, target.name, old_link, "",
                        f"ERROR: Lean file does not exist: {self._display_target(target)}"))
                    continue

                if not symbol:
                    if not target_exists:
                        issues.append(LinkIssue(md_path, line_no, target.name, old_link, "",
                            f"ERROR: Lean file does not exist: {self._display_target(target)}"))
                    elif self._is_absolute_file_link(full_url):
                        rel = self._display_target(target)
                        new_url = os.path.relpath(target, md_path.parent).replace(os.sep, "/")
                        issues.append(LinkIssue(md_path, line_no, target.name, old_link,
                            f"[{link_text}]({new_url})", f"Absolute local file link; use {rel}"))
                    continue

                decls = self.indexer.find_declarations(symbol)
                exact = [d for d in decls if d.file_path.resolve() == target.resolve()]
                if len(exact) == 1:
                    decl = exact[0]
                elif len(exact) > 1:
                    issues.append(LinkIssue(md_path, line_no, symbol, old_link, "",
                        f"ERROR: ambiguous declaration {symbol} in {self._display_target(target)}"))
                    continue
                elif len(decls) == 1:
                    decl = decls[0]
                elif len(decls) > 1:
                    missing = (
                        f"ERROR: Lean file does not exist: {self._display_target(target)}; "
                        if not target_exists else ""
                    )
                    issues.append(LinkIssue(md_path, line_no, symbol, old_link, "",
                        f"{missing}ERROR: ambiguous declaration {symbol}; target path does not disambiguate it"))
                    continue
                elif explicit or Path(link_text.strip()).stem != target.stem:
                    missing = (
                        f"ERROR: Lean file does not exist: {self._display_target(target)}; "
                        if not target_exists else ""
                    )
                    issues.append(LinkIssue(md_path, line_no, symbol, old_link, "",
                        f"{missing}ERROR: declaration {symbol} was not found in the indexed Lean sources"))
                    continue
                else:
                    if not target_exists:
                        issues.append(LinkIssue(md_path, line_no, target.name, old_link, "",
                            f"ERROR: Lean file does not exist: {self._display_target(target)}"))
                    continue

                actual_file = decl.file_path.resolve()
                cited_match = re.search(r"#L(\d+)", full_url)
                cited_line = int(cited_match.group(1)) if cited_match else None
                moved = actual_file != target.resolve()
                line_shifted = cited_line is not None and cited_line != decl.line_number
                needs_line = self.add_missing and cited_line is None
                if moved or line_shifted or needs_line or self._is_absolute_file_link(full_url):
                    new_url = self._compute_new_url(full_url, md_path, actual_file, decl.line_number)
                    reasons = []
                    if moved:
                        reasons.append(f"Moved: {self._display_target(target)} -> {self._display_target(actual_file)}")
                    if line_shifted:
                        reasons.append(f"Line shift: #L{cited_line} -> #L{decl.line_number}")
                    if needs_line:
                        reasons.append(f"Missing line number: added #L{decl.line_number}")
                    if self._is_absolute_file_link(full_url):
                        reasons.append("Absolute local file link")
                    issues.append(LinkIssue(md_path, line_no, symbol, old_link,
                        f"[{link_text}]({new_url})", "; ".join(reasons)))

        return issues

    def _extract_symbol(self, link_text: str, context_line: str) -> Optional[str]:
        clean = link_text.strip().strip("`").strip()
        # If the link text is clearly a file path/reference, do not treat it as a symbol
        if clean.endswith(".lean") or "/" in clean or "\\" in clean:
            return None

        # 1. Backticked symbol inside link text: [`name`]
        m_backtick = re.search(r"`([A-Za-z0-9_\'\.]+)`", link_text)
        if m_backtick:
            return m_backtick.group(1).split(".")[-1]

        # 2. Entire link text is a valid Lean identifier
        if re.match(r"^[A-Za-z0-9_\'\.]+$", clean):
            return clean.split(".")[-1]

        # 3. Check for Lean identifiers in backticks immediately preceding the link
        # e.g.: `symbol` ([link_text](...)) or `symbol`: [link_text](...)
        m_pre = re.search(r"`([A-Za-z0-9_\'\.]+)`\s*(?:[:(]\s*)?\[" + re.escape(link_text) + r"\]", context_line)
        if m_pre:
            sym = m_pre.group(1).split(".")[-1]
            if sym in self.indexer.by_name:
                return sym

        return None

    def _resolve_local_lean_path(self, md_path: Path, target: str) -> Optional[Path]:
        clean = target.strip().strip("<>")
        parsed = urlsplit(clean)
        if parsed.scheme in {"http", "https"}:
            if parsed.netloc.lower() not in {"github.com", "www.github.com"}:
                return None
            parts = [unquote(part) for part in parsed.path.split("/") if part]
            if len(parts) < 5 or parts[2] != "blob":
                return None
            owner_repo = "/".join(parts[:2]).lower()
            if owner_repo != "aleryberry/praxeology_lean":
                return None
            clean_path = "/".join(parts[4:])
        elif parsed.scheme == "file":
            clean_path = unquote(parsed.path)
        elif parsed.scheme:
            return None
        else:
            clean_path = unquote(parsed.path or clean.split("#", 1)[0].split("?", 1)[0])
        if not clean_path.endswith(".lean"):
            return None

        candidate = Path(clean_path)
        if candidate.is_absolute():
            return candidate.resolve()
        if clean_path.startswith("Praxeology/") or clean_path == "Praxeology.lean":
            return (self.root_dir / candidate).resolve()
        relative = (md_path.parent / candidate).resolve()
        if relative.exists():
            return relative
        return (self.root_dir / candidate).resolve()

    def _display_target(self, target: Path) -> str:
        try:
            return target.resolve().relative_to(self.root_dir).as_posix()
        except ValueError:
            return str(target.resolve())

    @staticmethod
    def _is_absolute_file_link(url: str) -> bool:
        parsed = urlsplit(url.strip().strip("<>"))
        return Path(unquote(parsed.path)).is_absolute() and parsed.scheme in {"", "file"}

    def _compute_new_url(self, full_url: str, md_path: Path, new_file: Path, new_line: int) -> str:
        relative = os.path.relpath(new_file, md_path.parent).replace(os.sep, "/")
        parsed = urlsplit(full_url.strip().strip("<>"))
        if parsed.scheme in {"http", "https"} and parsed.netloc.lower() in {"github.com", "www.github.com"}:
            prefix, marker, rest = parsed.path.partition("/blob/")
            if marker:
                ref, _, _old_path = rest.partition("/")
                relative = f"{prefix}/blob/{ref}/{self._display_target(new_file)}"
                return f"https://{parsed.netloc}{relative}#L{new_line}"
        return f"{relative}#L{new_line}"

    def fix_file(self, md_path: Path, issues: List[LinkIssue]) -> None:
        if not issues:
            return
        with open(md_path, "r", encoding="utf-8") as f:
            content = f.read()

        for issue in issues:
            if not issue.new_link:
                continue
            content = content.replace(issue.old_link, issue.new_link)

        with open(md_path, "w", encoding="utf-8") as f:
            f.write(content)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Audit and fix Lean theorem/declaration line numbers in Markdown links."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="Repository root directory (default: current directory).",
    )
    parser.add_argument(
        "--path",
        type=Path,
        help="Specific Markdown file or directory to inspect (default: scans entire repo).",
    )
    parser.add_argument(
        "--fix",
        action="store_true",
        help="Automatically fix outdated links in-place.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="CI mode: exit with code 1 if any outdated link is found, 0 otherwise.",
    )
    parser.add_argument(
        "--add-missing",
        action="store_true",
        help="Add line numbers to links that currently only point to .lean files without #L...",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Preview changes without writing to disk.",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Print verbose debugging information.",
    )

    args = parser.parse_args()
    root_dir = args.root.resolve()

    print(f"[*] Indexing Lean codebase in {root_dir / 'Praxeology'}...")
    indexer = LeanIndexer(root_dir)
    indexer.index()
    print(f"[✓] Indexed {len(indexer.by_name)} distinct Lean declaration symbols.")

    auditor = MarkdownLinkAuditor(indexer, root_dir, add_missing=args.add_missing)

    # Determine files to audit
    target_path = (args.path or root_dir).resolve()
    if target_path.is_file():
        md_files = [target_path] if target_path.suffix == ".md" else []
    else:
        md_files = [
            p
            for p in target_path.glob("**/*.md")
            if not any(part in p.parts for part in [".lake", ".git", "scripts"])
        ]

    print(f"[*] Scanning {len(md_files)} Markdown files for Lean theorem references...\n")

    total_issues = 0
    files_with_issues: Dict[Path, List[LinkIssue]] = {}

    for md_file in sorted(md_files):
        issues = auditor.audit_file(md_file)
        if issues:
            files_with_issues[md_file] = issues
            total_issues += len(issues)
            rel_file = md_file.relative_to(root_dir).as_posix()
            print(f"📄 {rel_file}: {len(issues)} outdated reference(s) found:")
            for issue in issues:
                print(f"   Line {issue.line_number}: [{issue.symbol}] ({issue.reason})")
                if args.verbose or args.dry_run:
                    print(f"     Old: {issue.old_link}")
                    print(f"     New: {issue.new_link}")

    print("\n" + "=" * 60)
    print(f"Audit Summary: {total_issues} outdated reference(s) in {len(files_with_issues)} file(s).")
    print("=" * 60)

    if args.fix:
        if args.dry_run:
            print("[!] Dry-run enabled: No files were modified.")
        else:
            print("[*] Applying automatic fixes to Markdown files...")
            for md_file, issues in files_with_issues.items():
                auditor.fix_file(md_file, issues)
                rel_file = md_file.relative_to(root_dir).as_posix()
                print(f"[✓] Fixed {len(issues)} link(s) in {rel_file}")
            print("[✓] All links updated successfully.")

    if args.check:
        if total_issues > 0:
            print(f"[✗] Check failed: {total_issues} outdated references detected.")
            return 1
        print("[✓] Check passed: All Lean links are fully up to date.")
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
