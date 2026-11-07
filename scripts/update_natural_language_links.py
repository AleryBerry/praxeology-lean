#!/usr/bin/env python3
"""
update_natural_language_links.py

A tool to index formal declarations (Theorems, Propositions, Definitions, Lemmas,
Corollaries, Assumptions, and Examples) across `natural_language/` and audit /
maintain cross-document links and references to them across all Markdown documents
(e.g., in `critiques/`, `spec/`, and `natural_language/`). Directly complements
`update_theorem_links.py` for natural-language prose.

Features:
- Indexes all 320+ formal declarations in `natural_language/*.md` with chapter numbers,
  item numbers, declaration types, canonical titles, file paths, line numbers, and GitHub anchor slugs.
- Validates cross-references in Markdown documents:
  * Detects references to non-existent item numbers.
  * Detects declaration type mismatches (e.g. citing Proposition 13.12 as Theorem 13.12).
  * Detects chapter mismatches (e.g. citing Chapter 10 for Theorem 7.5).
  * Detects title mismatches and finds the correct number by title lookup.
  * Validates and updates Markdown links (both header anchor slugs and `#L...` line targets).
- Auto-fix mode (`--fix`):
  * Corrects declaration types in-place.
  * Updates outdated line numbers and anchor slugs in Markdown links.
  * Corrects mismatched numbers when unambiguous title matches exist.
- Linkify mode (`--add-links` / `--linkify`):
  * Converts plain-text citations into clickable Markdown links pointing to the exact
    section header in `natural_language/` (supports GitHub heading slugs or `#L...` line targets).
- Unlink mode (`--remove-links` / `--unlink`):
  * Unwraps Markdown links back into clean plain text.
- Export mode (`--dump-index [markdown|json]`):
  * Exports the complete indexed dictionary of natural_language declarations.
- CI check mode (`--check`):
  * Exits with code 1 if any unknown reference, broken link, or outdated target is found.
"""

from __future__ import annotations

import argparse
import bisect
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple


VALID_TYPES = [
    "Definition",
    "Theorem",
    "Proposition",
    "Lemma",
    "Corollary",
    "Assumption",
    "Example",
]

TYPE_CANONICAL = {t.lower(): t for t in VALID_TYPES}
for t in VALID_TYPES:
    TYPE_CANONICAL[t.lower() + "s"] = t


def normalize_text(text: str) -> str:
    """Normalize text for fuzzy title matching: strip math formatting, punctuation, lower."""
    t = re.sub(r"\$([^$]+)\$", r"\1", text)
    t = re.sub(r"[*_`]", "", t)
    t = re.sub(r"[^\w\s]", " ", t)
    return " ".join(t.lower().split())


def github_slug(heading: str) -> str:
    """Generate GitHub-compatible markdown heading anchor slug."""
    # Strip leading hashes (#, ##, ###)
    h = re.sub(r"^#+\s*", "", heading).strip().lower()
    # Remove chars that are not alphanumeric, whitespace, or hyphen
    h = re.sub(r"[^\w\s-]", "", h)
    # Replace whitespace with hyphens
    h = re.sub(r"\s+", "-", h)
    return h


@dataclass
class NLDeclaration:
    chapter: int
    item_type: str
    number: str
    title: str
    file_path: Path
    line_number: int
    raw_heading: str

    @property
    def canonical_name(self) -> str:
        return f"{self.item_type} {self.number}"

    @property
    def full_name(self) -> str:
        return f"{self.item_type} {self.number} ({self.title})"

    @property
    def normalized_title(self) -> str:
        return normalize_text(self.title)

    @property
    def anchor_slug(self) -> str:
        return github_slug(self.raw_heading)


def spans_overlap(span1: Tuple[int, int], span2: Tuple[int, int]) -> bool:
    """Checks whether two character spans overlap."""
    return max(span1[0], span2[0]) < min(span1[1], span2[1])


def compute_relative_link(
    source_file: Path,
    target_decl: NLDeclaration,
    anchor_style: str = "slug",
) -> str:
    """Computes the relative URL from source_file to target_decl."""
    anchor = f"#{target_decl.anchor_slug}" if anchor_style == "slug" else f"#L{target_decl.line_number}"
    if source_file.resolve() == target_decl.file_path.resolve():
        return anchor
    rel = os.path.relpath(target_decl.file_path, source_file.parent)
    return f"{rel}{anchor}"


class NaturalLanguageIndexer:
    """Indexes all formal declarations in natural_language/*.md."""

    HEADING_PATTERN = re.compile(
        r"^###\s+(Definition|Theorem|Proposition|Lemma|Corollary|Assumption|Example)\s+"
        r"([0-9]+(?:\.[0-9]+[a-z0-9]*)?)\s*\((.+?)\)\s*$"
    )

    def __init__(self, root_dir: Path):
        self.root_dir = root_dir.resolve()
        self.nl_dir = self.root_dir / "natural_language"
        self.items_by_number: Dict[str, NLDeclaration] = {}
        self.items_by_chapter_and_num: Dict[Tuple[int, str], NLDeclaration] = {}
        self.items_by_norm_title: Dict[str, List[NLDeclaration]] = {}
        self.all_items: List[NLDeclaration] = []

    def index(self) -> None:
        chapter_files = sorted(self.nl_dir.glob("[0-9][0-9]_*.md"))
        for path in chapter_files:
            m_chap = re.match(r"^([0-9]{2})_", path.name)
            chapter_num = int(m_chap.group(1)) if m_chap else 0

            try:
                with open(path, "r", encoding="utf-8", errors="replace") as f:
                    lines = f.readlines()
            except OSError as e:
                print(f"[!] Warning: Could not read {path}: {e}", file=sys.stderr)
                continue

            for line_no, line in enumerate(lines, 1):
                m = self.HEADING_PATTERN.match(line.strip())
                if m:
                    decl_type, number, title = m.groups()
                    decl = NLDeclaration(
                        chapter=chapter_num,
                        item_type=decl_type,
                        number=number,
                        title=title.strip(),
                        file_path=path,
                        line_number=line_no,
                        raw_heading=line.strip(),
                    )
                    self.items_by_number[number] = decl
                    self.items_by_chapter_and_num[(chapter_num, number)] = decl
                    self.items_by_norm_title.setdefault(decl.normalized_title, []).append(decl)
                    self.all_items.append(decl)

    def find_by_number(self, number: str) -> Optional[NLDeclaration]:
        return self.items_by_number.get(number)

    def find_by_title(self, title: str) -> List[NLDeclaration]:
        norm = normalize_text(title)
        if not norm:
            return []
        if norm in self.items_by_norm_title:
            return self.items_by_norm_title[norm]
        matches = []
        for indexed_norm, decls in self.items_by_norm_title.items():
            if norm in indexed_norm or indexed_norm in norm:
                matches.extend(decls)
        return matches


@dataclass
class ReferenceIssue:
    file_path: Path
    line_number: int
    raw_text: str
    issue_type: str  # 'unknown_number', 'type_mismatch', 'chapter_mismatch', 'title_mismatch', 'broken_link', 'broken_slug', 'file_mismatch'
    message: str
    current_value: str
    suggested_value: Optional[str]
    span: Tuple[int, int]


class ReferenceAuditor:
    """Scans, audits, fixes, and linkifies references across Markdown documents."""

    # Matches references like:
    # Chapter 3, Theorem 3.4
    # Chapter 3 (Definitions 3.8–3.10)
    # Theorem 7.16 (Unified Positive Time Preference...)
    # Definition 9.14g
    REF_PATTERN = re.compile(
        r"(?P<chap_prefix>Chapter\s+(?P<chap_num>\d+)[,\s:]+(?:and\s+Chapter\s+\d+[,\s:]+)?)?"
        r"\b(?P<decl_type>Theorem|Proposition|Definition|Lemma|Corollary|Assumption|Example)s?\s+"
        r"(?P<number>[0-9]+\.[0-9]+[a-z0-9]*)"
        r"(?:\s*\((?P<title>[^)]+)\))?",
        re.IGNORECASE,
    )

    # Range pattern like Definitions 3.8–3.10 or Theorems 11.17-11.18
    RANGE_PATTERN = re.compile(
        r"\b(?P<decl_type>Theorems|Propositions|Definitions|Lemmas|Corollaries|Assumptions|Examples)\s+"
        r"(?P<num1>[0-9]+\.[0-9]+[a-z0-9]*)[–-](?P<num2>[0-9]+\.[0-9]+[a-z0-9]*)",
        re.IGNORECASE,
    )

    # Markdown link pattern to natural_language declarations
    LINK_PATTERN = re.compile(
        r"\[(?P<link_text>[^\]]+)\]\((?P<url>(?:[^)]*?)(?:(?P<filename>[0-9]{2}_[^)#]+\.md))?#(?:L(?P<line>\d+)|(?P<slug>[a-z0-9-]+)))\)"
    )

    # Patterns inside parentheticals that are NOT titles
    NON_TITLE_PAREN_PATTERN = re.compile(
        r"^(?:Chapter\s+\d+|Part\s+\d+|Section\s+\d+|see\s+|formerly\s+|e\.g\.|i\.e\.|strict\s+preference|definition\b|theorem\b)",
        re.IGNORECASE,
    )

    def __init__(self, indexer: NaturalLanguageIndexer, root_dir: Path):
        self.indexer = indexer
        self.root_dir = root_dir.resolve()

    def audit_file(self, file_path: Path) -> List[ReferenceIssue]:
        issues: List[ReferenceIssue] = []
        try:
            with open(file_path, "r", encoding="utf-8", errors="replace") as f:
                content = f.read()
        except OSError as e:
            print(f"[!] Warning: Could not read {file_path}: {e}", file=sys.stderr)
            return issues

        lines = content.splitlines(keepends=True)
        char_offsets = []
        curr = 0
        for line in lines:
            char_offsets.append(curr)
            curr += len(line)

        # 1. Audit Markdown links
        for m in self.LINK_PATTERN.finditer(content):
            start = m.start()
            line_no = self._offset_to_line(start, char_offsets)
            link_text = m.group("link_text")
            filename = m.group("filename")
            line_str = m.group("line")
            slug_str = m.group("slug")

            # Try to identify declaration number from link_text or slug
            m_num = re.search(r"\b([0-9]+\.[0-9]+[a-z0-9]*)\b", link_text)
            num = m_num.group(1) if m_num else None

            if not num and slug_str:
                m_slug_num = re.search(r"-(?:[0-9]+|[0-9]+\.[0-9]+[a-z0-9]*)-", slug_str)
                # match e.g. definition-11-... -> 1.1 or proposition-914g-... -> 9.14g
                # fallback check
                for d in self.indexer.all_items:
                    if d.anchor_slug == slug_str:
                        num = d.number
                        break

            if not num:
                continue

            decl = self.indexer.find_by_number(num)
            if not decl:
                issues.append(
                    ReferenceIssue(
                        file_path=file_path,
                        line_number=line_no,
                        raw_text=m.group(0),
                        issue_type="unknown_number",
                        message=f"Markdown link targets unknown declaration '{num}'",
                        current_value=num,
                        suggested_value=None,
                        span=(start, m.end()),
                    )
                )
            else:
                expected_file = decl.file_path.name
                if filename and filename != expected_file:
                    issues.append(
                        ReferenceIssue(
                            file_path=file_path,
                            line_number=line_no,
                            raw_text=m.group(0),
                            issue_type="file_mismatch",
                            message=f"Link targets '{filename}', but {decl.canonical_name} is in '{expected_file}'",
                            current_value=filename,
                            suggested_value=expected_file,
                            span=(start, m.end()),
                        )
                    )
                elif line_str and int(line_str) != decl.line_number:
                    issues.append(
                        ReferenceIssue(
                            file_path=file_path,
                            line_number=line_no,
                            raw_text=m.group(0),
                            issue_type="broken_link",
                            message=f"Line target #L{line_str} is outdated; {decl.canonical_name} is at line {decl.line_number}",
                            current_value=f"#L{line_str}",
                            suggested_value=f"#L{decl.line_number}",
                            span=(start, m.end()),
                        )
                    )
                elif slug_str and slug_str != decl.anchor_slug:
                    issues.append(
                        ReferenceIssue(
                            file_path=file_path,
                            line_number=line_no,
                            raw_text=m.group(0),
                            issue_type="broken_slug",
                            message=f"Anchor slug #{slug_str} does not match declared slug #{decl.anchor_slug}",
                            current_value=f"#{slug_str}",
                            suggested_value=f"#{decl.anchor_slug}",
                            span=(start, m.end()),
                        )
                    )

        # 2. Audit textual references
        for line_idx, line in enumerate(lines, 1):
            # Skip Markdown headings (defining titles/sections)
            if line.strip().startswith("#"):
                continue

            for m in self.REF_PATTERN.finditer(line):
                chap_num = int(m.group("chap_num")) if m.group("chap_num") else None
                decl_type_raw = m.group("decl_type")
                num = m.group("number")
                title_raw = m.group("title")

                # If parenthetical is actually a chapter indicator like (Chapter 1)
                if title_raw and re.match(r"^Chapter\s+(\d+)$", title_raw.strip(), re.IGNORECASE):
                    m_paren_chap = re.match(r"^Chapter\s+(\d+)$", title_raw.strip(), re.IGNORECASE)
                    if m_paren_chap:
                        chap_num = int(m_paren_chap.group(1))
                        title_raw = None

                start = m.start()
                end = m.end()

                decl = self.indexer.find_by_number(num)

                if not decl:
                    suggested = None
                    if title_raw and not self.NON_TITLE_PAREN_PATTERN.match(title_raw.strip()):
                        by_title = self.indexer.find_by_title(title_raw)
                        if by_title:
                            suggested = by_title[0].canonical_name

                    issues.append(
                        ReferenceIssue(
                            file_path=file_path,
                            line_number=line_idx,
                            raw_text=m.group(0),
                            issue_type="unknown_number",
                            message=f"Reference to non-existent item '{decl_type_raw} {num}'",
                            current_value=f"{decl_type_raw} {num}",
                            suggested_value=suggested,
                            span=(start, end),
                        )
                    )
                    continue

                # Check chapter mismatch
                if chap_num is not None and chap_num != decl.chapter:
                    issues.append(
                        ReferenceIssue(
                            file_path=file_path,
                            line_number=line_idx,
                            raw_text=m.group(0),
                            issue_type="chapter_mismatch",
                            message=f"Cited Chapter {chap_num}, but {decl.canonical_name} is in Chapter {decl.chapter}",
                            current_value=f"Chapter {chap_num}",
                            suggested_value=f"Chapter {decl.chapter}",
                            span=(start, end),
                        )
                    )

                # Check declaration type mismatch
                norm_cited_type = TYPE_CANONICAL.get(decl_type_raw.lower())
                if norm_cited_type and norm_cited_type != decl.item_type:
                    issues.append(
                        ReferenceIssue(
                            file_path=file_path,
                            line_number=line_idx,
                            raw_text=m.group(0),
                            issue_type="type_mismatch",
                            message=f"Cited as '{decl_type_raw} {num}', but declared as '{decl.item_type} {num}' ({decl.title})",
                            current_value=f"{decl_type_raw} {num}",
                            suggested_value=f"{decl.item_type} {num}",
                            span=(start, end),
                        )
                    )

                # Check title mismatch if title was explicitly provided
                if title_raw and not self.NON_TITLE_PAREN_PATTERN.match(title_raw.strip()):
                    norm_given = normalize_text(title_raw)
                    if (
                        len(norm_given.split()) >= 2
                        and norm_given not in decl.normalized_title
                        and decl.normalized_title not in norm_given
                    ):
                        alt_matches = self.indexer.find_by_title(title_raw)
                        alt_info = f" (title matches {alt_matches[0].full_name})" if alt_matches else ""
                        issues.append(
                            ReferenceIssue(
                                file_path=file_path,
                                line_number=line_idx,
                                raw_text=m.group(0),
                                issue_type="title_mismatch",
                                message=f"Title '({title_raw})' does not match declared title '({decl.title})'{alt_info}",
                                current_value=title_raw,
                                suggested_value=decl.title if not alt_matches else alt_matches[0].full_name,
                                span=(start, end),
                            )
                        )

        return issues

    def fix_file(self, file_path: Path, issues: List[ReferenceIssue]) -> int:
        """Applies automated in-place fixes for straightforward issues."""
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                lines = f.readlines()
        except OSError as e:
            print(f"[!] Warning: Could not read {file_path}: {e}", file=sys.stderr)
            return 0

        fixes_applied = 0
        issues_by_line: Dict[int, List[ReferenceIssue]] = {}
        for issue in issues:
            issues_by_line.setdefault(issue.line_number, []).append(issue)

        for line_no, line_issues in sorted(issues_by_line.items(), reverse=True):
            idx = line_no - 1
            line = lines[idx]

            for issue in line_issues:
                # Fix broken line targets in Markdown links
                if issue.issue_type == "broken_link" and issue.suggested_value:
                    if issue.current_value in line:
                        line = line.replace(issue.current_value, issue.suggested_value)
                        fixes_applied += 1

                # Fix broken anchor slugs in Markdown links
                elif issue.issue_type == "broken_slug" and issue.suggested_value:
                    if issue.current_value in line:
                        line = line.replace(issue.current_value, issue.suggested_value)
                        fixes_applied += 1

                # Fix declaration type mismatch
                elif issue.issue_type == "type_mismatch" and issue.suggested_value:
                    if issue.current_value in line:
                        line = line.replace(issue.current_value, issue.suggested_value, 1)
                        fixes_applied += 1

                # Fix chapter mismatch
                elif issue.issue_type == "chapter_mismatch" and issue.suggested_value:
                    if issue.current_value in line:
                        line = line.replace(issue.current_value, issue.suggested_value, 1)
                        fixes_applied += 1

                # Fix unknown number if unambiguous title match was found
                elif issue.issue_type == "unknown_number" and issue.suggested_value:
                    if issue.current_value in line:
                        line = line.replace(issue.current_value, issue.suggested_value, 1)
                        fixes_applied += 1

            lines[idx] = line

        if fixes_applied > 0:
            with open(file_path, "w", encoding="utf-8") as f:
                f.writelines(lines)

        return fixes_applied

    def linkify_file(
        self,
        file_path: Path,
        anchor_style: str = "slug",
        dry_run: bool = False,
    ) -> int:
        """
        Converts unlinked textual references in file_path into clickable Markdown links
        pointing to the corresponding natural_language declaration headers.
        """
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                lines = f.readlines()
        except OSError as e:
            print(f"[!] Warning: Could not read {file_path}: {e}", file=sys.stderr)
            return 0

        total_links_added = 0
        in_code_block = False

        for idx, line in enumerate(lines):
            stripped = line.strip()
            # Toggle fenced code blocks
            if stripped.startswith("```") or stripped.startswith("~~~"):
                in_code_block = not in_code_block
                continue

            if in_code_block:
                continue

            # Skip heading lines
            if stripped.startswith("#"):
                continue

            # Identify protected spans in this line (inline code, existing links, html tags)
            protected: List[Tuple[int, int]] = []
            for m in re.finditer(r"`[^`]+`|\[[^\]]+\]\([^)]+\)|<[^>]+>", line):
                protected.append((m.start(), m.end()))

            replacements: List[Tuple[int, int, str]] = []

            # 1. Range matches e.g. Definitions 3.8–3.10
            for m in self.RANGE_PATTERN.finditer(line):
                span = (m.start(), m.end())
                if any(spans_overlap(span, p) for p in protected):
                    continue
                d1 = self.indexer.find_by_number(m.group("num1"))
                d2 = self.indexer.find_by_number(m.group("num2"))
                if d1 and d2:
                    url1 = compute_relative_link(file_path, d1, anchor_style)
                    url2 = compute_relative_link(file_path, d2, anchor_style)
                    decl_type = m.group("decl_type")
                    repl = f"[{decl_type} {d1.number}]({url1})–[{d2.number}]({url2})"
                    replacements.append((span[0], span[1], repl))
                    protected.append(span)
                    total_links_added += 2

            # 2. Individual reference matches
            for m in self.REF_PATTERN.finditer(line):
                span_start = m.start("decl_type")
                num = m.group("number")
                d = self.indexer.find_by_number(num)
                if not d:
                    continue

                title = m.group("title")
                span_end = m.end("number")
                if title and not self.NON_TITLE_PAREN_PATTERN.match(title.strip()):
                    norm_given = normalize_text(title)
                    if (
                        len(norm_given.split()) >= 1
                        and (norm_given in d.normalized_title or d.normalized_title in norm_given)
                    ):
                        span_end = m.end()

                span = (span_start, span_end)
                if any(spans_overlap(span, p) for p in protected):
                    continue

                url = compute_relative_link(file_path, d, anchor_style)
                ref_text = line[span_start:span_end]
                repl = f"[{ref_text}]({url})"
                replacements.append((span_start, span_end, repl))
                protected.append(span)
                total_links_added += 1

            if replacements:
                # Apply replacements from right to left to preserve offsets
                new_line = line
                for start, end, repl in sorted(replacements, key=lambda x: x[0], reverse=True):
                    new_line = new_line[:start] + repl + new_line[end:]
                lines[idx] = new_line

        if total_links_added > 0 and not dry_run:
            with open(file_path, "w", encoding="utf-8") as f:
                f.writelines(lines)

        return total_links_added

    def unlink_file(self, file_path: Path, dry_run: bool = False) -> int:
        """
        Unwraps Markdown links pointing to natural_language declarations back into plain text.
        """
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
        except OSError as e:
            print(f"[!] Warning: Could not read {file_path}: {e}", file=sys.stderr)
            return 0

        unlinked_count = 0

        def unwrap_match(m: re.Match) -> str:
            nonlocal unlinked_count
            unlinked_count += 1
            return m.group("link_text")

        new_content = self.LINK_PATTERN.sub(unwrap_match, content)

        if unlinked_count > 0 and not dry_run:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(new_content)

        return unlinked_count

    def _offset_to_line(self, offset: int, char_offsets: List[int]) -> int:
        return bisect.bisect_right(char_offsets, offset)


def dump_index(indexer: NaturalLanguageIndexer, fmt: str = "markdown") -> str:
    """Exports the complete indexed dictionary of natural_language declarations."""
    if fmt == "json":
        items_data = [
            {
                "chapter": decl.chapter,
                "type": decl.item_type,
                "number": decl.number,
                "title": decl.title,
                "file": decl.file_path.name,
                "line": decl.line_number,
                "anchor_slug": decl.anchor_slug,
            }
            for decl in indexer.all_items
        ]
        return json.dumps(items_data, indent=2)

    # Markdown format
    lines = [
        "# Index of Formal Declarations in `natural_language/`",
        "",
        f"Total Indexed Declarations: **{len(indexer.all_items)}**",
        "",
        "| Chapter | Item Number | Type | Title | GitHub Anchor | File Reference |",
        "|---|---|---|---|---|---|",
    ]
    for decl in indexer.all_items:
        rel_link = f"[{decl.file_path.name}#L{decl.line_number}](../natural_language/{decl.file_path.name}#L{decl.line_number})"
        lines.append(
            f"| Chapter {decl.chapter} | **{decl.number}** | {decl.item_type} | {decl.title} | `#{decl.anchor_slug}` | {rel_link} |"
        )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Standardize, audit, and linkify formal references across Praxeology Markdown documents."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Root repository directory (defaults to repository root).",
    )
    parser.add_argument(
        "--path",
        type=Path,
        help="Specific directory or Markdown file to audit (defaults to entire repo).",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="CI mode: exit with non-zero code if any reference issues or broken links are found.",
    )
    parser.add_argument(
        "--fix",
        action="store_true",
        help="Automatically fix declaration types, chapter numbers, broken link targets, and outdated slugs in-place.",
    )
    parser.add_argument(
        "--add-links",
        "--linkify",
        action="store_true",
        help="Convert plain-text citations into clickable Markdown links pointing to natural_language declarations.",
    )
    parser.add_argument(
        "--remove-links",
        "--unlink",
        action="store_true",
        help="Unwrap Markdown links pointing to natural_language declarations back into plain text.",
    )
    parser.add_argument(
        "--anchor-style",
        choices=["slug", "line"],
        default="slug",
        help="Anchor style for generated links: 'slug' (header anchor slug, default) or 'line' (#L... line target).",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Preview changes without modifying files on disk.",
    )
    parser.add_argument(
        "--dump-index",
        choices=["markdown", "json"],
        help="Dump the complete index of declarations to stdout.",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Display detailed debugging information.",
    )

    args = parser.parse_args()
    root_dir = args.root.resolve()

    indexer = NaturalLanguageIndexer(root_dir)
    indexer.index()

    if args.dump_index:
        print(dump_index(indexer, args.dump_index))
        return 0

    print(f"[*] Indexed {len(indexer.all_items)} formal declarations across natural_language/.")

    auditor = ReferenceAuditor(indexer, root_dir)

    target_path = (args.path or root_dir).resolve()
    if target_path.is_file():
        md_files = [target_path] if target_path.suffix == ".md" else []
    else:
        md_files = [
            p
            for p in target_path.glob("**/*.md")
            if not any(part in p.parts for part in [".lake", ".git", "scripts", "node_modules"])
        ]

    # Handle --remove-links
    if args.remove_links:
        print(f"[*] Unlinking Markdown files ({len(md_files)} files)...")
        total_unlinked = 0
        for md_file in sorted(md_files):
            count = auditor.unlink_file(md_file, dry_run=args.dry_run)
            if count > 0:
                rel_file = md_file.relative_to(root_dir).as_posix()
                prefix = "[preview]" if args.dry_run else "[✓]"
                print(f"{prefix} Unlinked {count} reference(s) in {rel_file}")
                total_unlinked += count
        action = "would be removed" if args.dry_run else "total links removed"
        print(f"[✓] Finished unlinking: {total_unlinked} {action}.")
        return 0

    # Handle --add-links
    if args.add_links:
        print(f"[*] Converting plain-text references to clickable links ({len(md_files)} files, style: {args.anchor_style})...")
        total_linked = 0
        for md_file in sorted(md_files):
            count = auditor.linkify_file(md_file, anchor_style=args.anchor_style, dry_run=args.dry_run)
            if count > 0:
                rel_file = md_file.relative_to(root_dir).as_posix()
                prefix = "[preview]" if args.dry_run else "[✓]"
                print(f"{prefix} Added {count} link(s) to {rel_file}")
                total_linked += count
        action = "would be added" if args.dry_run else "total links added"
        print(f"[✓] Finished linkification: {total_linked} {action}.")
        return 0

    print(f"[*] Scanning {len(md_files)} Markdown files for formal references...\n")

    total_issues = 0
    files_with_issues: Dict[Path, List[ReferenceIssue]] = {}

    for md_file in sorted(md_files):
        issues = auditor.audit_file(md_file)
        if issues:
            files_with_issues[md_file] = issues
            total_issues += len(issues)
            rel_file = md_file.relative_to(root_dir).as_posix()
            print(f"📄 {rel_file}: {len(issues)} issue(s) found:")
            for issue in issues:
                fix_hint = f" -> Suggestion: {issue.suggested_value}" if issue.suggested_value else ""
                print(f"   Line {issue.line_number} [{issue.issue_type}]: {issue.message}{fix_hint}")

    print("\n" + "=" * 60)
    print(f"Audit Summary: {total_issues} issue(s) detected across {len(files_with_issues)} file(s).")
    print("=" * 60)

    if args.fix:
        if args.dry_run:
            print("[!] Dry-run enabled: No files were modified.")
        else:
            print("[*] Applying automatic fixes to Markdown files...")
            fixed_count = 0
            for md_file, issues in files_with_issues.items():
                n_fixed = auditor.fix_file(md_file, issues)
                if n_fixed > 0:
                    rel_file = md_file.relative_to(root_dir).as_posix()
                    print(f"[✓] Fixed {n_fixed} issue(s) in {rel_file}")
                    fixed_count += n_fixed
            print(f"[✓] Completed fixes: {fixed_count} issue(s) resolved.")

    if args.check:
        critical_issues = sum(
            1
            for issues in files_with_issues.values()
            for i in issues
            if i.issue_type in ["unknown_number", "broken_link", "broken_slug", "chapter_mismatch", "file_mismatch"]
        )
        if critical_issues > 0:
            print(f"[✗] Check failed: {critical_issues} critical reference issue(s) detected.")
            return 1
        print("[✓] Check passed: All formal references and links are valid.")
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
