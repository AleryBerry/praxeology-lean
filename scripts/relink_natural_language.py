#!/usr/bin/env python3
"""
relink_natural_language.py

A unified framework to automatically relink cross-document references, Markdown links,
and citations to `natural_language/` declarations after reworking or renumbering chapters.

Features:
- Semantic Title & Slug Resolution: When chapter restructuring shifts declaration numbers
  (e.g., Theorem 8.24 -> Theorem 8.27), the framework extracts title semantics from link
  anchors or parentheticals, maps them to current declarations, and updates both the link text
  and target URL atomically.
- Legacy Alias Support: Seamlessly maps historical, merged, or renamed declaration titles
  to current canonical targets.
- Atomic In-Place Patching: Replaces outdated links and plain-text references in-place
  without corrupting surrounding Markdown, code blocks, or inline formatting.
- Gatekeeper Mode (`--check`): Exits with code 1 if any broken references or outdated links exist.
- Preview Modes: Supports `--dry-run` and `--diff` for inspecting proposed changes.

Usage:
    # Automatically fix and relink all references across the repository
    python3 scripts/relink_natural_language.py

    # Preview relinking changes without modifying files
    python3 scripts/relink_natural_language.py --dry-run

    # Show unified diff of proposed relinking changes
    python3 scripts/relink_natural_language.py --diff

    # Verify all references are clean (CI mode)
    python3 scripts/relink_natural_language.py --check
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

VALID_TYPES = [
    "Axiom",
    "Definition",
    "Theorem",
    "Proposition",
    "Lemma",
    "Corollary",
    "Witness",
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
    t = re.sub(r"[^\w\s-]", " ", t)
    return " ".join(t.lower().replace("-", " ").split())


def github_slug(heading: str) -> str:
    """Generate GitHub-compatible markdown heading anchor slug."""
    h = re.sub(r"^#+\s*", "", heading).strip().lower()
    h = re.sub(r"[^\w\s-]", "", h)
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
        r"^###\s+(Axiom|Definition|Theorem|Proposition|Lemma|Corollary|Witness|Assumption|Example)\s+"
        r"([0-9]+(?:\.[0-9]+[a-z0-9]*)?)\s*\((.+?)\)\s*$"
    )

    LEGACY_ALIASES: Dict[str, str] = {
        # Chapter 8 interaction taxonomy rework
        "the-three-interaction-categories-partition-theorem": "Pairwise Mutual Exclusivity of Bilateral Interaction Predicates",
        "three-interaction-categories-partition-theorem": "Pairwise Mutual Exclusivity of Bilateral Interaction Predicates",
        "the-three-interaction-categories-partition": "Pairwise Mutual Exclusivity of Bilateral Interaction Predicates",
        "three-interaction-categories-partition": "Pairwise Mutual Exclusivity of Bilateral Interaction Predicates",
        "the three interaction categories partition theorem": "Pairwise Mutual Exclusivity of Bilateral Interaction Predicates",
        "three interaction categories partition theorem": "Pairwise Mutual Exclusivity of Bilateral Interaction Predicates",
        "peaceful-competition-excludes-anchored-extortion": "Pairwise Mutual Exclusivity of Bilateral Interaction Predicates",
        "peaceful competition excludes anchored extortion": "Pairwise Mutual Exclusivity of Bilateral Interaction Predicates",
        "three-interaction-categories": "Bilateral Interaction Predicates",
        "the-three-interaction-categories": "Bilateral Interaction Predicates",
        # Chapter 8 menu stripping title alias
        "the-coercive-menu-stripping-equivalence-theorem": "The Coercive Menu-Stripping Equivalence Theorem",
        "coercive-menu-stripping-equivalence-theorem": "The Coercive Menu-Stripping Equivalence Theorem",
        # Chapter 12 title alias
        "purposeful-fiscal-choice-under-the-stated-bounds": "A Beneficiary Requires a Loss in a Zero-Yield Cohort",
        "purposeful fiscal choice under the stated bounds": "A Beneficiary Requires a Loss in a Zero-Yield Cohort",
        # Chapter 2 transition law title alias
        "physical-transition-balance-law": "Physical Matter Conservation and Inventory Transition",
        "physical transition balance law": "Physical Matter Conservation and Inventory Transition",
    }

    def __init__(self, root_dir: Path):
        self.root_dir = root_dir.resolve()
        self.nl_dir = self.root_dir / "natural_language"
        self.items_by_number: Dict[str, NLDeclaration] = {}
        self.items_by_chapter_and_num: Dict[Tuple[int, str], NLDeclaration] = {}
        self.items_by_norm_title: Dict[str, List[NLDeclaration]] = {}
        self.items_by_title_slug: Dict[str, NLDeclaration] = {}
        self.chapters_by_num: Dict[int, NLDeclaration] = {}
        self.chapters_by_slug: Dict[str, NLDeclaration] = {}
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
                stripped = line.strip()
                m_chap_head = re.match(r"^#\s+Chapter\s+([0-9]+):\s*(.+?)\s*$", stripped, re.I)
                if m_chap_head:
                    c_num_str, c_title = m_chap_head.groups()
                    c_num = int(c_num_str)
                    decl = NLDeclaration(
                        chapter=c_num,
                        item_type="Chapter",
                        number=c_num_str,
                        title=c_title.strip(),
                        file_path=path,
                        line_number=line_no,
                        raw_heading=stripped,
                    )
                    self.chapters_by_num[c_num] = decl
                    self.chapters_by_slug[decl.anchor_slug] = decl
                    continue

                m = self.HEADING_PATTERN.match(stripped)
                if m:
                    decl_type, number, title = m.groups()
                    decl = NLDeclaration(
                        chapter=chapter_num,
                        item_type=decl_type,
                        number=number,
                        title=title.strip(),
                        file_path=path,
                        line_number=line_no,
                        raw_heading=stripped,
                    )
                    self.items_by_number[number] = decl
                    self.items_by_chapter_and_num[(chapter_num, number)] = decl
                    self.items_by_norm_title.setdefault(decl.normalized_title, []).append(decl)
                    self.all_items.append(decl)

                    # Index by title slug (slug stripped of type and number)
                    slug_title = re.sub(
                        r"^(?:axiom|definition|theorem|proposition|lemma|corollary|witness|assumption|example)-(?:[0-9]+(?:\.[0-9]+[a-z0-9]*)?|[0-9]+)-",
                        "",
                        decl.anchor_slug,
                    )
                    self.items_by_title_slug[slug_title] = decl
                    if slug_title.startswith("the-"):
                        self.items_by_title_slug[slug_title[4:]] = decl

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

    def resolve_declaration(
        self,
        slug: Optional[str] = None,
        link_text: Optional[str] = None,
        number_hint: Optional[str] = None,
        file_hint: Optional[str] = None,
    ) -> Optional[NLDeclaration]:
        """
        Resolves the intended formal declaration from link target slug, link text,
        or declaration number hint, using title semantics and legacy aliases.
        """
        # 0. Chapter-level resolution
        if slug:
            slug_clean = slug.strip().lower()
            if slug_clean in self.chapters_by_slug:
                return self.chapters_by_slug[slug_clean]
            m_sc = re.match(r"^chapter-([0-9]+)(?:-(.+))?$", slug_clean)
            if m_sc:
                c_num = int(m_sc.group(1))
                if c_num in self.chapters_by_num:
                    return self.chapters_by_num[c_num]

        if link_text:
            m_ct = re.match(r"^Chapter\s+([0-9]+)\b", link_text.strip(), re.I)
            if m_ct:
                c_num = int(m_ct.group(1))
                if c_num in self.chapters_by_num:
                    return self.chapters_by_num[c_num]

        # 1. Try slug title extraction
        if slug:
            slug_clean = slug.strip().lower()
            slug_title = re.sub(
                r"^(?:axiom|definition|theorem|proposition|lemma|corollary|witness|assumption|example)-(?:[0-9]+(?:\.[0-9]+[a-z0-9]*)?|[0-9]+)-",
                "",
                slug_clean,
            )
            if slug_title in self.items_by_title_slug:
                return self.items_by_title_slug[slug_title]
            if slug_title.removeprefix("the-") in self.items_by_title_slug:
                return self.items_by_title_slug[slug_title.removeprefix("the-")]

            if slug_title in self.LEGACY_ALIASES:
                target_title = self.LEGACY_ALIASES[slug_title]
                matches = self.find_by_title(target_title)
                if matches:
                    return matches[0]

            words = slug_title.replace("-", " ").strip()
            if len(words.split()) >= 2:
                matches = self.find_by_title(words)
                if matches:
                    return matches[0]

        # 2. Try link text parenthetical title extraction
        if link_text:
            m_paren = re.search(r"\(([^)]+)\)", link_text)
            if m_paren:
                paren_title = m_paren.group(1).strip()
                if not re.match(r"^(?:Chapter\s+\d+|Part\s+\d+|Section\s+\d+|see\s+|formerly\s+|e\.g\.)", paren_title, re.I):
                    matches = self.find_by_title(paren_title)
                    if matches:
                        return matches[0]
                    norm_paren = normalize_text(paren_title)
                    if norm_paren in self.LEGACY_ALIASES:
                        target = self.LEGACY_ALIASES[norm_paren]
                        matches = self.find_by_title(target)
                        if matches:
                            return matches[0]

        # 3. Exact anchor slug match
        if slug:
            for decl in self.all_items:
                if decl.anchor_slug == slug.strip().lower():
                    return decl

        # 4. Fallback to number lookup
        if number_hint:
            if file_hint:
                m_chap = re.match(r"^([0-9]{2})_", file_hint)
                if m_chap:
                    chap_num = int(m_chap.group(1))
                    if (chap_num, number_hint) in self.items_by_chapter_and_num:
                        return self.items_by_chapter_and_num[(chap_num, number_hint)]
            return self.find_by_number(number_hint)

        return None


@dataclass
class ReferenceIssue:
    file_path: Path
    line_number: int
    raw_text: str
    issue_type: str  # 'outdated_link', 'unknown_number', 'type_mismatch', 'chapter_mismatch', 'renumbered_text'
    message: str
    current_value: str
    suggested_value: Optional[str]
    span: Tuple[int, int]


class ReferenceAuditor:
    """Scans, audits, fixes, and relinks references across Markdown documents."""

    REF_PATTERN = re.compile(
        r"(?P<chap_prefix>Chapter\s+(?P<chap_num>\d+)[,\s:]+(?:and\s+Chapter\s+\d+[,\s:]+)?)?"
        r"\b(?P<decl_type>Axiom|Theorem|Proposition|Definition|Lemma|Corollary|Witness|Assumption|Example)s?\s+"
        r"(?P<number>[0-9]+\.[0-9]+[a-z0-9]*)"
        r"(?:\s*\((?P<title>[^)]+)\))?",
        re.IGNORECASE,
    )

    RANGE_PATTERN = re.compile(
        r"\b(?P<decl_type>Axioms|Theorems|Propositions|Definitions|Lemmas|Corollaries|Witnesses|Assumptions|Examples)\s+"
        r"(?P<num1>[0-9]+\.[0-9]+[a-z0-9]*)[–-](?P<num2>[0-9]+\.[0-9]+[a-z0-9]*)",
        re.IGNORECASE,
    )

    LINK_PATTERN = re.compile(
        r"\[(?P<link_text>[^\]]+)\]\((?P<url>(?:[^)]*?)(?:(?P<filename>[0-9]{2}_[^)#]+\.md))?#(?:L(?P<line>\d+)|(?P<slug>[a-z0-9-]+)))\)"
    )

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
        link_spans: List[Tuple[int, int]] = []
        is_in_nl = file_path.parent.name == "natural_language"

        for m in self.LINK_PATTERN.finditer(content):
            filename = m.group("filename")
            slug_str = m.group("slug")
            line_str = m.group("line")

            # Only audit links pointing to natural_language/
            if not filename and not is_in_nl:
                continue

            start = m.start()
            end = m.end()
            link_spans.append((start, end))
            line_no = self._offset_to_line(start, char_offsets)
            link_text = m.group("link_text")

            # Extract declaration number hint
            m_num = re.search(r"\b([0-9]+\.[0-9]+[a-z0-9]*)\b", link_text)
            num = m_num.group(1) if m_num else None

            decl = self.indexer.resolve_declaration(
                slug=slug_str,
                link_text=link_text,
                number_hint=num,
                file_hint=filename,
            )

            if not decl:
                issues.append(
                    ReferenceIssue(
                        file_path=file_path,
                        line_number=line_no,
                        raw_text=m.group(0),
                        issue_type="unknown_number",
                        message=f"Markdown link targets unknown declaration '{num or slug_str}'",
                        current_value=m.group(0),
                        suggested_value=None,
                        span=(start, end),
                    )
                )
                continue

            # Compute canonical URL and updated link text
            expected_url = compute_relative_link(file_path, decl, anchor_style="slug" if slug_str else "line")

            new_link_text = link_text
            if decl.item_type != "Chapter":
                if num and num != decl.number:
                    new_link_text = re.sub(r"\b" + re.escape(num) + r"\b", decl.number, new_link_text)

                m_type = re.search(
                    r"\b(Axiom|Theorem|Proposition|Definition|Lemma|Corollary|Witness|Assumption|Example)s?\b",
                    new_link_text,
                    re.I,
                )
                if m_type:
                    old_t = m_type.group(1)
                    norm_old = TYPE_CANONICAL.get(old_t.lower())
                    if norm_old and norm_old != decl.item_type:
                        new_link_text = re.sub(r"\b" + re.escape(old_t) + r"\b", decl.item_type, new_link_text, count=1)

            new_raw_link = f"[{new_link_text}]({expected_url})"

            if new_raw_link != m.group(0):
                if line_str and int(line_str) != decl.line_number:
                    issue_type = "broken_link"
                    msg = f"Line target #L{line_str} is outdated; {decl.canonical_name} is at line {decl.line_number}"
                elif filename and filename != decl.file_path.name:
                    issue_type = "file_mismatch"
                    msg = f"Link targets '{filename}', but {decl.canonical_name} is in '{decl.file_path.name}'"
                elif num and num != decl.number:
                    issue_type = "outdated_link"
                    msg = f"Link targets outdated reference -> {decl.canonical_name} ({decl.title})"
                elif slug_str and slug_str != decl.anchor_slug:
                    issue_type = "broken_slug"
                    msg = f"Anchor slug #{slug_str} does not match declared slug #{decl.anchor_slug}"
                else:
                    issue_type = "outdated_link"
                    msg = f"Link targets outdated reference -> {decl.canonical_name} ({decl.title})"

                issues.append(
                    ReferenceIssue(
                        file_path=file_path,
                        line_number=line_no,
                        raw_text=m.group(0),
                        issue_type=issue_type,
                        message=msg,
                        current_value=m.group(0),
                        suggested_value=new_raw_link,
                        span=(start, end),
                    )
                )

        # 2. Audit textual references (outside links and code blocks)
        for line_idx, line in enumerate(lines, 1):
            if line.strip().startswith("#"):
                continue

            line_start_char = char_offsets[line_idx - 1]

            for m in self.REF_PATTERN.finditer(line):
                global_start = line_start_char + m.start()
                global_end = line_start_char + m.end()

                if any(spans_overlap((global_start, global_end), lspan) for lspan in link_spans):
                    continue

                chap_num = int(m.group("chap_num")) if m.group("chap_num") else None
                decl_type_raw = m.group("decl_type")
                num = m.group("number")
                title_raw = m.group("title")

                if title_raw and re.match(r"^Chapter\s+(\d+)$", title_raw.strip(), re.IGNORECASE):
                    m_paren_chap = re.match(r"^Chapter\s+(\d+)$", title_raw.strip(), re.IGNORECASE)
                    if m_paren_chap:
                        chap_num = int(m_paren_chap.group(1))
                        title_raw = None

                decl = None
                if title_raw and not self.NON_TITLE_PAREN_PATTERN.match(title_raw.strip()):
                    matches = self.indexer.find_by_title(title_raw)
                    if matches:
                        decl = matches[0]
                    else:
                        norm_t = normalize_text(title_raw)
                        if norm_t in self.indexer.LEGACY_ALIASES:
                            t_matches = self.indexer.find_by_title(self.indexer.LEGACY_ALIASES[norm_t])
                            if t_matches:
                                decl = t_matches[0]

                if not decl:
                    decl = self.indexer.find_by_number(num)

                if not decl:
                    issues.append(
                        ReferenceIssue(
                            file_path=file_path,
                            line_number=line_idx,
                            raw_text=m.group(0),
                            issue_type="unknown_number",
                            message=f"Reference to non-existent item '{decl_type_raw} {num}'",
                            current_value=f"{decl_type_raw} {num}",
                            suggested_value=None,
                            span=(global_start, global_end),
                        )
                    )
                    continue

                if decl.number != num:
                    new_ref = f"{decl.item_type} {decl.number}" + (f" ({decl.title})" if title_raw else "")
                    issues.append(
                        ReferenceIssue(
                            file_path=file_path,
                            line_number=line_idx,
                            raw_text=m.group(0),
                            issue_type="renumbered_text",
                            message=f"Cited as '{decl_type_raw} {num}', but title matches '{decl.canonical_name}' ({decl.title})",
                            current_value=m.group(0),
                            suggested_value=new_ref,
                            span=(global_start, global_end),
                        )
                    )
                    continue

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
                            span=(global_start, global_end),
                        )
                    )

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
                            span=(global_start, global_end),
                        )
                    )

        return issues

    def fix_file(self, file_path: Path, issues: List[ReferenceIssue]) -> int:
        """Applies automated in-place fixes for link and reference issues."""
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

            # Sort by span start position in reverse so right-most changes happen first
            line_issues.sort(key=lambda i: i.span[0] if i.span else 0, reverse=True)

            for issue in line_issues:
                if issue.issue_type in ["outdated_link", "broken_link", "broken_slug", "file_mismatch", "renumbered_text"]:
                    if issue.suggested_value and issue.current_value in line:
                        line = line.replace(issue.current_value, issue.suggested_value, 1)
                        fixes_applied += 1
                elif issue.issue_type in ["type_mismatch", "chapter_mismatch", "unknown_number"]:
                    if issue.suggested_value and issue.current_value in line:
                        line = line.replace(issue.current_value, issue.suggested_value, 1)
                        fixes_applied += 1

            lines[idx] = line

        if fixes_applied > 0:
            with open(file_path, "w", encoding="utf-8") as f:
                f.writelines(lines)

        return fixes_applied

    def preview_diff(self, file_path: Path, issues: List[ReferenceIssue]) -> List[str]:
        """Generates unified diff lines representing proposed fixes."""
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                original_lines = f.readlines()
        except OSError:
            return []

        modified_lines = list(original_lines)
        issues_by_line: Dict[int, List[ReferenceIssue]] = {}
        for issue in issues:
            issues_by_line.setdefault(issue.line_number, []).append(issue)

        for line_no, line_issues in sorted(issues_by_line.items(), reverse=True):
            idx = line_no - 1
            line = modified_lines[idx]
            line_issues.sort(key=lambda i: i.span[0] if i.span else 0, reverse=True)

            for issue in line_issues:
                if issue.suggested_value and issue.current_value in line:
                    line = line.replace(issue.current_value, issue.suggested_value, 1)

            modified_lines[idx] = line

        return list(
            difflib.unified_diff(
                original_lines,
                modified_lines,
                fromfile=str(file_path),
                tofile=str(file_path),
                lineterm="",
            )
        )

    def _offset_to_line(self, offset: int, char_offsets: List[int]) -> int:
        import bisect
        return bisect.bisect_right(char_offsets, offset)


def relink_all(
    root_dir: Path,
    target_path: Optional[Path] = None,
    check: bool = False,
    dry_run: bool = False,
    diff: bool = False,
    verbose: bool = False,
) -> int:
    """Core framework driver: indexes natural_language/ and relinks references across Markdown docs."""
    indexer = NaturalLanguageIndexer(root_dir)
    indexer.index()
    print(f"[*] Indexed {len(indexer.all_items)} formal declarations across natural_language/.")

    auditor = ReferenceAuditor(indexer, root_dir)
    search_dir = (target_path or root_dir).resolve()

    if search_dir.is_file():
        md_files = [search_dir] if search_dir.suffix == ".md" else []
    else:
        md_files = [
            p
            for p in search_dir.glob("**/*.md")
            if not any(part in p.parts for part in [".lake", ".git", "scripts", "node_modules"])
        ]

    print(f"[*] Scanning {len(md_files)} Markdown files for references to natural_language/...\n")

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
                fix_hint = f" -> Relink: {issue.suggested_value}" if issue.suggested_value else ""
                print(f"   Line {issue.line_number} [{issue.issue_type}]: {issue.message}{fix_hint}")

    print("\n" + "=" * 60)
    print(f"Relinking Audit: {total_issues} reference(s) to relink across {len(files_with_issues)} file(s).")
    print("=" * 60)

    if diff:
        print("\nUnified Diff of Proposed Changes:\n")
        for md_file, issues in files_with_issues.items():
            diff_lines = auditor.preview_diff(md_file, issues)
            for d in diff_lines:
                print(d)
        return 0

    if check:
        critical = sum(
            1
            for issues in files_with_issues.values()
            for i in issues
            if i.issue_type in ["unknown_number", "outdated_link", "broken_link", "broken_slug", "chapter_mismatch", "file_mismatch"]
        )
        if critical > 0:
            print(f"[✗] Check failed: {critical} reference(s) require relinking.")
            return 1
        print("[✓] Check passed: All formal references and links are valid.")
        return 0

    # Default action: relink / fix
    if dry_run:
        print("[!] Dry-run enabled: No files were modified.")
        return 0

    print("[*] Applying automatic relinking across Markdown files...")
    fixed_count = 0
    for md_file, issues in files_with_issues.items():
        n_fixed = auditor.fix_file(md_file, issues)
        if n_fixed > 0:
            rel_file = md_file.relative_to(root_dir).as_posix()
            print(f"[✓] Relinked {n_fixed} reference(s) in {rel_file}")
            fixed_count += n_fixed

    print(f"\n[✓] Relinking complete: {fixed_count} reference(s) successfully updated.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Unified framework to automatically relink cross-document references after reworking natural_language/."
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
        help="Specific directory or Markdown file to relink (defaults to entire repo).",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="CI mode: exit with code 1 if any references need relinking, 0 if clean.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Preview changes without modifying files on disk.",
    )
    parser.add_argument(
        "--diff",
        action="store_true",
        help="Output unified diff of proposed relinking changes.",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Display detailed debugging information.",
    )

    args = parser.parse_args()
    return relink_all(
        root_dir=args.root.resolve(),
        target_path=args.path,
        check=args.check,
        dry_run=args.dry_run,
        diff=args.diff,
        verbose=args.verbose,
    )


if __name__ == "__main__":
    sys.exit(main())
