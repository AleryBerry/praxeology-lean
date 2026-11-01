#!/usr/bin/env python3
"""
fix_markdown_math.py

A tool to identify and automatically fix KaTeX / GitHub Flavored Markdown math
formatting errors across Markdown documentation.

Features:
1. Replaces disallowed KaTeX macros (e.g., `\\operatorname{...}` -> `\\text{...}`).
2. Unindents indented display math code blocks (e.g. `   ```math` -> ````math`),
   which otherwise fail to render as KaTeX display equations in Markdown lists.
3. Fixes hyphens inside `\\text{...}` in math mode (e.g. `\\text{functional-form}`
   -> `\\text{functional form}`), which cause minus-sign rendering artifacts in KaTeX.
4. Escapes raw currency dollar signs (e.g. `$50` -> `\\$50`), which inadvertently
   trigger inline math parser errors.
5. Rewrites unbraced `^*` superscripts in inline math as `^{\\ast}` so Markdown
   cannot consume the star as an emphasis marker.
6. Moves same-line `$$...$$` display math into proper blocks, keeps display math
   out of lists, braces malformed parenthesized `^_` superscripts, adds missing
   subscripts to calligraphic set labels, repairs unescaped delimiter braces
   after `\\left`, `\\right`, and `\\middle` (`\\left{` -> `\\left\\{`, `\\right}` -> `\\right\\}`),
   and repairs malformed `aligned` row breaks.
7. Ensures proper spacing before and after display math blocks.
8. Provides `--check` mode for CI, `--fix` for automatic patching, and `--dry-run`
   for previewing diffs.
"""

from __future__ import annotations

import argparse
import difflib
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple


@dataclass
class MathIssue:
    file_path: Path
    line_number: int
    rule: str
    description: str
    original: str
    fixed: str


class MarkdownMathFixer:
    """Detects and fixes Markdown math syntax issues."""

    # Matches \operatorname{...} or \operatorname*{...}
    OPERATORNAME_RE = re.compile(r"\\operatorname\*?\{([A-Za-z0-9_]+)\}")

    # Matches hyphens inside \text{...} in math mode
    TEXT_HYPHEN_RE = re.compile(r"\\text\{([A-Za-z0-9_]+(?:-[A-Za-z0-9_]+)+)\}")

    # Matches raw monetary currency signs like $50 or $100 not preceded by \ or `
    CURRENCY_RE = re.compile(
        r"(?<!\\)(?<!`)\$(?!`)([0-9]{1,3}(?:,[0-9]{3})+(?:\.[0-9]+)?|[0-9]+(?:\.[0-9]+)?(?:\s*(?:k|M|B|billion|million|trillion))?)"
    )

    INLINE_DISPLAY_LINE_RE = re.compile(
        r"^(?P<indent>[ \t]*)(?P<quote>[\"']?)\$\$(?P<body>.*?)\$\$(?P=quote)[ \t]*(?:\r?\n)?$"
    )
    INLINE_DISPLAY_PAIR_RE = re.compile(r"(?<!\\)\$\$.*?(?<!\\)\$\$")
    UNSUBSCRIPTED_MATHCAL_TEXT_RE = re.compile(
        r"(\\mathcal\s*\{[^{}]+\})\s*\{\s*\\text\s*\{([^{}]+)\}\s*\}"
    )
    ALIGNED_ROW_SEPARATOR_RE = re.compile(r"(?<!\\)\\[ \t]+&")
    ALIGNED_SINGLE_ROW_BREAK_RE = re.compile(r"(?<!\\)\\[ \t]*\r?\n[ \t]*&")
    LIST_ITEM_RE = re.compile(r"^(?P<indent> *)(?P<marker>[-+*]|\d+[.)])(?P<gap> +)")
    INLINE_TEX_RE = re.compile(
        r"(?<!\\)(?<!\$)\$(?!\$)(?P<body>(?:\\.|[^$\n])+?)(?<!\\)\$(?!\$)"
    )
    INLINE_BACKTICK_MATH_RE = re.compile(r"(?<!\\)\$`(?P<body>[^`\n]*)`\$")
    PROSE_MATH_COMMAND_RE = re.compile(
        r"\\(triangleright|succ|mathsf|mathcal|mathrm|mathbb|mathit|mathbf|"
        r"forall|exists|in|notin|wedge|vee|neg|implies|iff|prec|le|leq|"
        r"ge|geq|neq|equiv|alpha|beta|gamma|delta|rho|sigma|tau|phi|omega)(?![A-Za-z])"
    )
    CORRUPTED_TEXT_COMMAND_RE = re.compile(r"\text\{")
    STAR_SUPERSCRIPT_RE = re.compile(r"(?<!\\)\^(?:\{([^{}]*)\*([^{}]*)\}|\*)")
    UNBRACED_STAR_SUPERSCRIPT_RE = STAR_SUPERSCRIPT_RE
    PARENTHESIZED_INLINE_MATH_FULL_RE = re.compile(
        r"\(\$(?![$\`])(?P<body>[^\n$]*\([^\n$]*\)[^\n$]*?)(?<!\\)\$\)"
    )
    PARENTHESIZED_INLINE_MATH_OPEN_RE = re.compile(
        r"\(\$(?![$\`])(?P<body>[^\n$]*\([^\n$]*\)[^\n$]*?)(?<!\\)\$"
    )
    PARENTHESIZED_INLINE_MATH_CLOSE_RE = re.compile(
        r"(?<!\\)\$(?![$\`])(?P<body>[^\n$]*\([^\n$]*\)[^\n$]*?)(?<!\\)\$\)"
    )
    PARENTHESIZED_INLINE_MATH_PRECEDING_RE = re.compile(
        r"(\([^()\n$]+(?<!\\)\$(?![$\`])[^$\n]+?(?<!\\)\$)\)"
    )
    PARENTHESIZED_INLINE_MATH_RE = PARENTHESIZED_INLINE_MATH_FULL_RE
    MATRIX_ENV_RE = re.compile(
        r"(\\begin\s*\{(?P<env>(?:p|b|B|v|V)?matrix|cases|array)\}(?:\{[^{}]*\})?)(?P<body>.*?)(\\end\s*\{(?P=env)\})",
        re.DOTALL,
    )
    UNSPACED_RELATIONAL_OPERATOR_RE = re.compile(
        r"(?<=[A-Za-z0-9_\})])[<>][A-Za-z]|(?<=[ \t])[<>][A-Za-z]|(?<=[A-Za-z0-9_\})])[<>](?=[ \t])"
    )
    UNESCAPED_DELIMITER_BRACE_RE = re.compile(
        r"\\(left|right|middle)\s*(\\)?([{}])"
    )
    CORRUPTED_EX_ANTE_RE = re.compile(r"\\mathrm\{ex\s+ext\{-\}ante\}")
    OVERESCAPED_PROOF_SYMBOL_RE = re.compile(r"\\\\(square|blacksquare)\b")
    UNBRACED_PAREN_SUPERSCRIPT_RE = re.compile(r"\^_\s*(?P<group>\([^()\n]*\))")
    VULNERABLE_INLINE_MATH_PUNCT_RE = re.compile(r"[^a-zA-Z0-9\\][ \t]*_")
    PROSE_REPAIRS = (
        (re.compile(r"\bagent s\b"), "agent's"),
        (re.compile(r"\bRicardo s\b"), "Ricardo's"),
        (re.compile(r"\bmodel s\b"), "model's"),
        (re.compile(r"\bseller s\b"), "seller's"),
        (re.compile(r"\bB\s+hm-Bawerk\b"), "Böhm-Bawerk"),
    )
    INLINE_CODE_SPAN_RE = re.compile(r"(?<!`)(`+)(?!`)(.*?)(?<!`)\1(?!`)")

    def __init__(self, root_dir: Path):
        self.root_dir = root_dir.resolve()

    @staticmethod
    def is_escaped(text: str, index: int) -> bool:
        slashes = 0
        index -= 1
        while index >= 0 and text[index] == "\\":
            slashes += 1
            index -= 1
        return slashes % 2 == 1

    @classmethod
    def is_vulnerable_inline_math(cls, body: str) -> bool:
        """Return whether inline dollar math is vulnerable to CommonMark mangling."""
        if r"\{" in body or r"\}" in body:
            return True
        if r"\_" in body:
            return True
        if r"\," in body:
            return True
        if r"\$" in body:
            return True
        if r"\\" in body:
            return True
        if r"\begin{" in body:
            return True
        return bool(cls.VULNERABLE_INLINE_MATH_PUNCT_RE.search(body))

    @classmethod
    def tex_atom_end(cls, source: str, start: int) -> int | None:
        while start < len(source) and source[start].isspace():
            start += 1
        if start >= len(source):
            return None
        if source[start] == "{":
            depth = 1
            cursor = start + 1
            while cursor < len(source):
                if not cls.is_escaped(source, cursor):
                    if source[cursor] == "{":
                        depth += 1
                    elif source[cursor] == "}":
                        depth -= 1
                        if depth == 0:
                            return cursor + 1
                cursor += 1
            return None
        if source[start] == "\\":
            cursor = start + 1
            if cursor >= len(source):
                return None
            if source[cursor].isalpha():
                while cursor < len(source) and source[cursor].isalpha():
                    cursor += 1
                return cursor
            return cursor + 1
        return start + 1

    @classmethod
    def repair_double_subscripts(cls, source: str) -> tuple[str, bool]:
        replacements: list[tuple[int, int, str]] = []
        cursor = 0
        while cursor < len(source):
            if source[cursor] != "_" or cls.is_escaped(source, cursor):
                cursor += 1
                continue
            first_end = cls.tex_atom_end(source, cursor + 1)
            if first_end is None:
                cursor += 1
                continue
            second_start = first_end
            while second_start < len(source) and source[second_start].isspace():
                second_start += 1
            if second_start >= len(source) or source[second_start] != "_" or cls.is_escaped(source, second_start):
                cursor = first_end
                continue
            second_end = cls.tex_atom_end(source, second_start + 1)
            if second_end is None:
                cursor = second_start + 1
                continue
            first_arg_start = cursor + 1
            while first_arg_start < first_end and source[first_arg_start].isspace():
                first_arg_start += 1
            second_arg_start = second_start + 1
            while second_arg_start < second_end and source[second_arg_start].isspace():
                second_arg_start += 1
            first_arg = source[first_arg_start:first_end]
            second_arg = source[second_arg_start:second_end]
            if first_arg.startswith("{") and first_arg.endswith("}"):
                first_arg = first_arg[1:-1]
            if second_arg.startswith("{") and second_arg.endswith("}"):
                second_arg = second_arg[1:-1]
            replacements.append((cursor, second_end, f"_{{{first_arg},{second_arg}}}"))
            cursor = second_end
        for start, end, replacement in reversed(replacements):
            source = source[:start] + replacement + source[end:]
        return source, bool(replacements)

    @classmethod
    def repair_matrix_rows(cls, tex: str) -> tuple[str, bool]:
        any_fixed = False
        while True:
            step_fixed = False

            def _fix_env(match: re.Match) -> str:
                nonlocal step_fixed
                prefix = match.group(1)
                body = match.group("body")
                suffix = match.group(4)
                new_body = re.sub(r"(?<!\\)\\[ \t]*\r?\n", lambda _: "\\\\\n", body)
                new_body = re.sub(r"(?<!\\)\\[ \t]+", lambda _: "\\\\ ", new_body)
                if new_body != body:
                    step_fixed = True
                return prefix + new_body + suffix

            tex = cls.MATRIX_ENV_RE.sub(_fix_env, tex)
            if not step_fixed:
                break
            any_fixed = True
        return tex, any_fixed

    @classmethod
    def repair_tex_body(cls, body: str) -> tuple[str, set[str]]:
        rules: set[str] = set()
        body, matrix_fixed = cls.repair_matrix_rows(body)
        if matrix_fixed:
            rules.add("malformed-matrix-row-separator")
        repaired = cls.CORRUPTED_TEXT_COMMAND_RE.sub(r"\\text{", body)
        if repaired != body:
            rules.add("corrupted-text-command")
        body = repaired
        repaired = cls.CORRUPTED_EX_ANTE_RE.sub(r"\\mathrm{ex\\text{-}ante}", body)
        if repaired != body:
            rules.add("corrupted-ex-ante-label")
        body = repaired
        repaired = cls.OVERESCAPED_PROOF_SYMBOL_RE.sub(
            lambda match: "\\" + match.group(1), body
        )
        if repaired != body:
            rules.add("overescaped-proof-symbol")
        body = repaired
        repaired = cls.UNBRACED_PAREN_SUPERSCRIPT_RE.sub(
            lambda match: match.group(0)
            if cls.is_escaped(body, match.start())
            else "^{" + match.group("group") + "}",
            body,
        )
        if repaired != body:
            rules.add("missing-open-brace-superscript")
        body = repaired
        body, double_fixed = cls.repair_double_subscripts(body)
        if double_fixed:
            rules.add("double-subscript")
        repaired_amp = re.sub(
            r"(\\text\s*\{)([^{}]*)(\})",
            lambda m: m.group(1) + re.sub(r"\s*\\?&(?:amp;)?\s*", "", m.group(2)) + m.group(3),
            body,
        )
        if repaired_amp != body:
            rules.add("ampersand-in-text")
            body = repaired_amp

        def replace_star_superscript(match: re.Match) -> str:
            if match.group(1) is not None:
                inner = (match.group(1) + r"\ast" + match.group(2)).strip()
                return f"^{{{inner}}}"
            return r"^{\ast}"

        repaired_stars = cls.STAR_SUPERSCRIPT_RE.sub(replace_star_superscript, body)
        if repaired_stars != body:
            rules.add("unbraced-star-superscript")
            body = repaired_stars

        def replace_delimiter_brace(match: re.Match) -> str:
            if cls.is_escaped(body, match.start()):
                return match.group(0)
            cmd = match.group(1)
            brace = match.group(3)
            b_name = "lbrace" if brace == "{" else "rbrace"
            return f"\\{cmd}\\{b_name}"

        repaired_delims = cls.UNESCAPED_DELIMITER_BRACE_RE.sub(
            replace_delimiter_brace, body
        )
        if repaired_delims != body:
            rules.add("unescaped-delimiter-brace")
            body = repaired_delims

        repaired_ops = re.sub(r"(?<=[A-Za-z0-9_\})])([<>])([A-Za-z])", r" \1 \2", body)
        repaired_ops = re.sub(r"([ \t])([<>])([A-Za-z])", r"\1\2 \3", repaired_ops)
        repaired_ops = re.sub(r"(?<=[A-Za-z0-9_\})])([<>])([ \t])", r" \1\2", repaired_ops)
        if repaired_ops != body:
            rules.add("unspaced-relational-operator")
            body = repaired_ops

        return body, rules

    @classmethod
    def normalize_display_body(cls, body: str) -> tuple[str, bool, bool, set[str]]:
        """Repair common set-label and aligned-row mistakes in display math."""
        body, tex_rules = cls.repair_tex_body(body)

        def set_label(match: re.Match) -> str:
            return f"{match.group(1)}_{{\\text{{{match.group(2)}}}}}"

        normalized = cls.UNSUBSCRIPTED_MATHCAL_TEXT_RE.sub(set_label, body)
        set_label_fixed = normalized != body
        body = normalized
        row_separator_fixed = False

        if r"\begin{aligned}" in body and r"\end{aligned}" in body:
            normalized, replacements = cls.ALIGNED_ROW_SEPARATOR_RE.subn(
                lambda _match: "\\\\\n&", body
            )
            normalized, single_breaks = cls.ALIGNED_SINGLE_ROW_BREAK_RE.subn(
                lambda _match: "\\\\\n&", normalized
            )
            row_separator_fixed = replacements > 0 or single_breaks > 0
            body = normalized

        body_lines = body.splitlines()
        while body_lines and not body_lines[0].strip():
            body_lines.pop(0)
        while body_lines and not body_lines[-1].strip():
            body_lines.pop()
        body = "\n".join(part.rstrip() for part in body_lines)
        return body, set_label_fixed, row_separator_fixed, tex_rules

    @classmethod
    def display_indent(cls, current_indent: str, previous_lines: List[str]) -> str:
        """Keep repaired display math at the document level."""
        return ""

    @staticmethod
    def mask_inline_code(text: str) -> str:
        """Mask Markdown code spans so their literal dollar signs are ignored."""
        chars = list(text)
        # Backticks inside `$`...`$` math are delimiters, not code-span
        # markers. Hide complete math spans before pairing ordinary code ticks.
        for match in MarkdownMathFixer.INLINE_BACKTICK_MATH_RE.finditer(text):
            for position in range(*match.span()):
                chars[position] = " "
        index = 0
        while index < len(text):
            if chars[index] != "`":
                index += 1
                continue
            run_end = index
            while run_end < len(text) and text[run_end] == "`":
                run_end += 1
            run_length = run_end - index
            if index > 0 and text[index - 1] == "$":
                index = run_end
                continue

            search = run_end
            closing: tuple[int, int] | None = None
            while search < len(text):
                candidate = next(
                    (position for position in range(search, len(text)) if chars[position] == "`"),
                    -1,
                )
                if candidate < 0:
                    break
                candidate_end = candidate
                while candidate_end < len(text) and chars[candidate_end] == "`":
                    candidate_end += 1
                if candidate_end - candidate == run_length:
                    closing = (candidate, candidate_end)
                    break
                search = candidate_end

            if closing is None:
                index = run_end
                continue
            for position in range(index, closing[1]):
                chars[position] = " "
            index = closing[1]
        return "".join(chars)

    @classmethod
    def apply_outside_inline_code(cls, text: str, pattern: re.Pattern, replacement) -> str:
        """Apply a math rewrite to prose/math while preserving inline code spans."""
        parts: List[str] = []
        cursor = 0
        for match in cls.INLINE_CODE_SPAN_RE.finditer(text):
            if match.start() > 0 and text[match.start() - 1] == "$":
                continue
            parts.append(pattern.sub(replacement, text[cursor : match.start()]))
            parts.append(match.group(0))
            cursor = match.end()
        parts.append(pattern.sub(replacement, text[cursor:]))
        return "".join(parts)

    @classmethod
    def repair_markdown_line(cls, line: str, in_math_block: bool) -> tuple[str, set[str]]:
        rules: set[str] = set()
        if in_math_block:
            repaired, tex_rules = cls.repair_tex_body(line)
            return repaired, tex_rules

        repaired_parens = cls.PARENTHESIZED_INLINE_MATH_FULL_RE.sub(
            r"( $\g<body>$ )", line
        )
        if repaired_parens != line:
            rules.add("parenthesized-inline-math")
            line = repaired_parens

        repaired_open = cls.PARENTHESIZED_INLINE_MATH_OPEN_RE.sub(
            r"( $\g<body>$", line
        )
        if repaired_open != line:
            rules.add("parenthesized-inline-math")
            line = repaired_open

        repaired_close = cls.PARENTHESIZED_INLINE_MATH_CLOSE_RE.sub(
            r"$\g<body>$ )", line
        )
        if repaired_close != line:
            rules.add("parenthesized-inline-math")
            line = repaired_close

        repaired_preceding = cls.PARENTHESIZED_INLINE_MATH_PRECEDING_RE.sub(
            r"\g<1> )", line
        )
        if repaired_preceding != line:
            rules.add("parenthesized-inline-math")
            line = repaired_preceding

        # Some repository pages use `$`...`$` as an inline-math delimiter.
        # Keep those TeX spans out of the prose repair below so commands such
        # as `\alpha` are not wrapped in nested dollar signs.
        for match in reversed(list(cls.INLINE_BACKTICK_MATH_RE.finditer(line))):
            body = match.group("body")
            repaired, body_rules = cls.repair_tex_body(body)
            if repaired != body:
                line = line[:match.start("body")] + repaired + line[match.end("body"):]
                rules.update(body_rules)

        backtick_math_spans = {
            match.span() for match in cls.INLINE_BACKTICK_MATH_RE.finditer(line)
        }
        visible = cls.mask_inline_code(line)
        inline_matches = list(cls.INLINE_TEX_RE.finditer(visible))
        for match in reversed(inline_matches):
            if match.span() in backtick_math_spans:
                continue
            body = match.group("body")
            if body is None:
                continue
            repaired, body_rules = cls.repair_tex_body(body)
            if cls.is_vulnerable_inline_math(repaired):
                start, end = match.span()
                is_paren = (
                    start > 0
                    and line[start - 1] == "("
                    and end < len(line)
                    and line[end] == ")"
                )
                if is_paren:
                    replacement = f"( $`{repaired}`$ )"
                    line = line[: start - 1] + replacement + line[end + 1 :]
                else:
                    replacement = f"$`{repaired}`$"
                    line = line[:start] + replacement + line[end:]
                rules.add("unprotected-inline-math")
                rules.update(body_rules)
                visible = cls.mask_inline_code(line)
            elif repaired != body:
                line = line[:match.start("body")] + repaired + line[match.end("body"):]
                rules.update(body_rules)
                visible = cls.mask_inline_code(line)

        visible = cls.mask_inline_code(line)
        math_spans = [match.span() for match in cls.INLINE_TEX_RE.finditer(visible)]
        math_spans.extend(
            match.span() for match in cls.INLINE_BACKTICK_MATH_RE.finditer(line)
        )
        prose_only = list(visible)
        for start, end in math_spans:
            for index in range(start, end):
                prose_only[index] = " "
        prose_only_text = "".join(prose_only)

        replacements: list[tuple[int, int, str, str]] = []
        for match in cls.PROSE_MATH_COMMAND_RE.finditer(prose_only_text):
            replacements.append((match.start(), match.end(), "$" + match.group(0) + "$", "math-command-outside-math"))
        for pattern, replacement in cls.PROSE_REPAIRS:
            for match in pattern.finditer(prose_only_text):
                replacements.append((match.start(), match.end(), replacement, "missing-apostrophe-or-character"))

        for start, end, replacement, rule in sorted(replacements, reverse=True):
            line = line[:start] + replacement + line[end:]
            rules.add(rule)
        return line, rules

    def audit_file(self, file_path: Path) -> Tuple[List[MathIssue], str]:
        issues: List[MathIssue] = []
        try:
            with open(file_path, "r", encoding="utf-8", errors="replace") as f:
                content = f.read()
        except OSError as e:
            print(f"[!] Warning: Could not read {file_path}: {e}", file=sys.stderr)
            return issues, ""

        lines = content.splitlines(keepends=True)
        new_lines: List[str] = []
        in_code_block = False
        in_math_block = False
        math_block_indent = 0
        code_fence_char = ""

        idx = 0
        while idx < len(lines):
            line = lines[idx]
            stripped = line.strip()
            line_no = idx + 1

            # Some Markdown renderers fail to process display math nested in a
            # list. Move top-level list equations outside the list, and attach
            # equations in nested lists to their item as inline math.
            if not in_code_block and not in_math_block and stripped == "$$":
                opening_indent = len(line) - len(line.lstrip(" "))
                if opening_indent == 0:
                    closing_idx = idx + 1
                    while closing_idx < len(lines) and lines[closing_idx].strip() != "$$":
                        closing_idx += 1
                    if closing_idx < len(lines):
                        original_body = "".join(lines[idx + 1 : closing_idx])
                        body, set_label_fixed, row_separator_fixed, tex_rules = self.normalize_display_body(
                            original_body
                        )
                        if body != original_body.strip():
                            fixed_lines = ["$$\n"]
                            fixed_lines.extend(f"{part}\n" for part in body.splitlines())
                            fixed_lines.append("$$\n")
                            fixed_block = "".join(fixed_lines)
                            original_block = "".join(lines[idx : closing_idx + 1])
                            new_lines.extend(fixed_lines)
                            rules = set(tex_rules)
                            if set_label_fixed:
                                rules.add("missing-set-label-subscript")
                            if row_separator_fixed:
                                rules.add("malformed-aligned-row-separator")
                            if not rules:
                                rules.add("display-math-formatting")
                            for rule in sorted(rules):
                                issues.append(
                                    MathIssue(
                                        file_path=file_path,
                                        line_number=line_no,
                                        rule=rule,
                                        description=f"Repaired the {rule.replace('-', ' ')} in display math.",
                                        original=original_block,
                                        fixed=fixed_block,
                                    )
                                )
                        else:
                            new_lines.extend(lines[idx : closing_idx + 1])
                        idx = closing_idx + 1
                        continue
                if opening_indent > 0:
                    closing_idx = idx + 1
                    while closing_idx < len(lines) and lines[closing_idx].strip() != "$$":
                        closing_idx += 1
                    if closing_idx < len(lines):
                        body_lines = [
                            part[opening_indent:]
                            if part.startswith(" " * opening_indent)
                            else part.lstrip()
                            for part in lines[idx + 1 : closing_idx]
                        ]
                        body, set_label_fixed, row_separator_fixed, tex_rules = self.normalize_display_body(
                            "\n".join(body_lines)
                        )
                        original_block = "".join(lines[idx : closing_idx + 1])

                        previous_index = len(new_lines) - 1
                        while previous_index >= 0 and not new_lines[previous_index].strip():
                            previous_index -= 1
                        list_item = None
                        scan_index = previous_index
                        while scan_index >= 0:
                            scan_line = new_lines[scan_index].rstrip("\r\n")
                            if not scan_line.strip():
                                scan_index -= 1
                                continue
                            matched = self.LIST_ITEM_RE.match(scan_line)
                            if matched:
                                list_item = matched
                                break
                            if not scan_line.startswith(" ") and not scan_line.startswith("\t"):
                                break
                            scan_index -= 1
                        nested_item = bool(
                            list_item and len(list_item.group("indent")) > 0
                        )

                        if nested_item and previous_index >= 0:
                            while new_lines and not new_lines[-1].strip():
                                new_lines.pop()
                            inline_body = " ".join(body.splitlines())
                            new_lines[-1] = new_lines[-1].rstrip("\r\n") + f" ${inline_body}$\n"
                            fixed_block = new_lines[-1]
                        else:
                            display_lines = ["$$\n"]
                            display_lines.extend(f"{part}\n" for part in body.splitlines())
                            display_lines.append("$$\n")
                            if new_lines and new_lines[-1].strip():
                                new_lines.append("\n")
                            new_lines.extend(display_lines)
                            if closing_idx + 1 < len(lines) and lines[closing_idx + 1].strip():
                                new_lines.append("\n")
                            fixed_block = "".join(display_lines)

                        issues.append(
                            MathIssue(
                                file_path=file_path,
                                line_number=line_no,
                                rule="display-math-in-list-item",
                                description=(
                                    "Moved display math out of a list item for renderer compatibility."
                                    if not nested_item
                                    else "Converted nested-list display math to inline math."
                                ),
                                original=original_block,
                                fixed=fixed_block,
                            )
                        )
                        if set_label_fixed:
                            issues.append(
                                MathIssue(
                                    file_path=file_path,
                                    line_number=line_no,
                                    rule="missing-set-label-subscript",
                                    description="Added the missing subscript before a calligraphic set label.",
                                    original=original_block,
                                    fixed=fixed_block,
                                )
                            )
                        if row_separator_fixed:
                            issues.append(
                                MathIssue(
                                    file_path=file_path,
                                    line_number=line_no,
                                    rule="malformed-aligned-row-separator",
                                    description="Repaired the aligned environment row break.",
                                    original=original_block,
                                    fixed=fixed_block,
                                )
                            )
                        for rule in sorted(tex_rules):
                            issues.append(
                                MathIssue(
                                    file_path=file_path,
                                    line_number=line_no,
                                    rule=rule,
                                    description=f"Repaired the {rule.replace('-', ' ')} in display math.",
                                    original=original_block,
                                    fixed=fixed_block,
                                )
                            )
                        idx = closing_idx + 1
                        continue

            # Check code block fences
            if stripped.startswith("```"):
                fence_tag = stripped[3:].strip()
                if not in_code_block and not in_math_block:
                    if fence_tag == "math":
                        in_math_block = True
                        leading_spaces = len(line) - len(line.lstrip(" "))
                        math_block_indent = leading_spaces
                        if leading_spaces > 0:
                            # Indented math fence!
                            fixed_line = "```math\n"
                            issues.append(
                                MathIssue(
                                    file_path=file_path,
                                    line_number=line_no,
                                    rule="indented-math-block",
                                    description=f"Math block indented by {leading_spaces} spaces (breaks display KaTeX rendering).",
                                    original=line,
                                    fixed=fixed_line,
                                )
                            )
                            # Ensure preceding blank line if not first line
                            if new_lines and new_lines[-1].strip() != "":
                                new_lines.append("\n")
                            new_lines.append(fixed_line)
                            idx += 1
                            continue
                        else:
                            in_code_block = False
                    else:
                        in_code_block = True
                        code_fence_char = stripped[:3]
                elif in_math_block and stripped == "```":
                    in_math_block = False
                    if math_block_indent > 0:
                        fixed_line = "```\n"
                        issues.append(
                            MathIssue(
                                file_path=file_path,
                                line_number=line_no,
                                rule="indented-math-block",
                                description=f"Closing math block fence indented by {math_block_indent} spaces.",
                                original=line,
                                fixed=fixed_line,
                            )
                        )
                        new_lines.append(fixed_line)
                        # Ensure blank line after math block if next line is not blank
                        if idx + 1 < len(lines) and lines[idx + 1].strip() != "" and not lines[idx + 1].strip().startswith("```"):
                            new_lines.append("\n")
                        math_block_indent = 0
                    else:
                        new_lines.append(line)
                    idx += 1
                    continue
                elif in_code_block and stripped.startswith(code_fence_char):
                    in_code_block = False

            # If inside a math block that was indented, strip the indentation
            if in_math_block and math_block_indent > 0:
                current_indent = len(line) - len(line.lstrip(" "))
                strip_amount = min(current_indent, math_block_indent)
                unindented = line[strip_amount:]
            else:
                unindented = line

            line_content = unindented.rstrip("\r\n")
            if not in_code_block and not in_math_block:
                visible_line = self.mask_inline_code(line_content)
                display_match = self.INLINE_DISPLAY_LINE_RE.match(visible_line)
                if display_match:
                    display_match = self.INLINE_DISPLAY_LINE_RE.match(line_content)
                    assert display_match is not None
                    original_body = display_match.group("body").strip()
                    body, set_label_fixed, row_separator_fixed, tex_rules = self.normalize_display_body(original_body)
                    indent = self.display_indent(display_match.group("indent"), new_lines)
                    display_lines = [f"{indent}$$\n"]
                    display_lines.extend(f"{indent}{part}\n" for part in body.splitlines())
                    display_lines.append(f"{indent}$$\n")
                    fixed_display = "".join(display_lines)
                    quote_note = " Removed surrounding quotation marks." if display_match.group("quote") else ""

                    issues.append(
                        MathIssue(
                            file_path=file_path,
                            line_number=line_no,
                            rule="inline-display-math",
                            description="Moved same-line display math delimiters onto their own lines." + quote_note,
                            original=line,
                            fixed=fixed_display,
                        )
                    )
                    if set_label_fixed:
                        issues.append(
                            MathIssue(
                                file_path=file_path,
                                line_number=line_no,
                                rule="missing-set-label-subscript",
                                description="Added the missing subscript before the set label.",
                                original=line,
                                fixed=fixed_display,
                            )
                        )
                    if row_separator_fixed:
                        issues.append(
                            MathIssue(
                                file_path=file_path,
                                line_number=line_no,
                                rule="malformed-aligned-row-separator",
                                description="Replaced a single backslash with a row break before the next aligned row.",
                                original=line,
                                fixed=fixed_display,
                            )
                        )
                    for rule in sorted(tex_rules):
                        issues.append(
                            MathIssue(
                                file_path=file_path,
                                line_number=line_no,
                                rule=rule,
                                description=f"Repaired the {rule.replace('-', ' ')} in display math.",
                                original=line,
                                fixed=fixed_display,
                            )
                        )

                    if new_lines and new_lines[-1].strip():
                        new_lines.append("\n")
                    new_lines.extend(display_lines)
                    if idx + 1 < len(lines) and lines[idx + 1].strip():
                        new_lines.append("\n")
                    idx += 1
                    continue

                if self.INLINE_DISPLAY_PAIR_RE.search(visible_line):
                    issues.append(
                        MathIssue(
                            file_path=file_path,
                            line_number=line_no,
                            rule="inline-display-math",
                            description="Display delimiters share a line with prose; move the equation to its own display block.",
                            original=line,
                            fixed=line,
                        )
                    )

            # Check inside math block or inline math
            modified_line = unindented

            if not in_code_block and not in_math_block and "$" in modified_line and not stripped.startswith("```"):
                leading_spaces = len(modified_line) - len(modified_line.lstrip(" "))
                if leading_spaces >= 4 and not self.LIST_ITEM_RE.match(modified_line.lstrip()):
                    unindented_math = "   " + modified_line.lstrip(" ")
                    issues.append(
                        MathIssue(
                            file_path=file_path,
                            line_number=line_no,
                            rule="indented-prose-math",
                            description=f"Reduced indentation of math prose line from {leading_spaces} spaces to 3 spaces to prevent GitHub from parsing it as an indented code block.",
                            original=modified_line,
                            fixed=unindented_math,
                        )
                    )
                    modified_line = unindented_math

            if not in_code_block:
                def _fix_set_label(match: re.Match) -> str:
                    return f"{match.group(1)}_{{\\text{{{match.group(2)}}}}}"

                new_val = self.apply_outside_inline_code(
                    modified_line, self.UNSUBSCRIPTED_MATHCAL_TEXT_RE, _fix_set_label
                )
                if new_val != modified_line:
                    issues.append(
                        MathIssue(
                            file_path=file_path,
                            line_number=line_no,
                            rule="missing-set-label-subscript",
                            description="Added the missing subscript before a calligraphic set label.",
                            original=modified_line,
                            fixed=new_val,
                        )
                    )
                    modified_line = new_val

                if self.ALIGNED_ROW_SEPARATOR_RE.search(
                    self.mask_inline_code(modified_line)
                ):
                    new_val = self.apply_outside_inline_code(
                        modified_line,
                        self.ALIGNED_ROW_SEPARATOR_RE,
                        lambda _match: "\\\\\n&",
                    )
                    issues.append(
                        MathIssue(
                            file_path=file_path,
                            line_number=line_no,
                            rule="malformed-aligned-row-separator",
                            description="Inserted a TeX row break before the next aligned row.",
                            original=modified_line,
                            fixed=new_val,
                        )
                    )
                    modified_line = new_val

            # 1. Fix \operatorname{...} -> \text{...}
            if "\\operatorname" in modified_line:
                def _rep_op(m: re.Match) -> str:
                    return f"\\text{{{m.group(1)}}}"
                new_val = self.apply_outside_inline_code(
                    modified_line, self.OPERATORNAME_RE, _rep_op
                )
                if new_val != modified_line:
                    issues.append(
                        MathIssue(
                            file_path=file_path,
                            line_number=line_no,
                            rule="disallowed-operatorname",
                            description="Replaced disallowed \\operatorname macro with \\text.",
                            original=modified_line,
                            fixed=new_val,
                        )
                    )
                    modified_line = new_val

            # 2. Fix hyphens inside \text{...} in math mode
            if "\\text{" in modified_line and "-" in modified_line:
                def _rep_hyphen(m: re.Match) -> str:
                    # Replace hyphen with space inside \text{...}
                    fixed_text = m.group(1).replace("-", " ")
                    return f"\\text{{{fixed_text}}}"
                new_val = self.apply_outside_inline_code(
                    modified_line, self.TEXT_HYPHEN_RE, _rep_hyphen
                )
                if new_val != modified_line:
                    issues.append(
                        MathIssue(
                            file_path=file_path,
                            line_number=line_no,
                            rule="text-hyphen-in-math",
                            description="Replaced hyphen in \\text{...} with space to avoid minus-sign font artifacts.",
                            original=modified_line,
                            fixed=new_val,
                        )
                    )
                    modified_line = new_val

            # 3. Check for raw unescaped currency dollar signs (outside code blocks)
            if not in_code_block and not in_math_block and "$" in modified_line:
                # Check if this line contains raw $50 etc. not in inline math $`...`$ or `...`
                # Only touch lines where $ is followed by a digit and not escaped
                def _rep_curr(m: re.Match) -> str:
                    return f"\\${m.group(1)}"

                def _looks_like_inline_math(m: re.Match, text: str) -> bool:
                    # A number can begin a valid inline formula (for example,
                    # `$1$` or `$5\leq 6$`). Preserve it when the next
                    # unescaped dollar closes math and the intervening text
                    # has mathematical syntax. This avoids turning a math
                    # delimiter into a literal currency sign.
                    close = m.end()
                    while close < len(text):
                        close = text.find("$", close)
                        if close < 0:
                            return False
                        slashes = 0
                        cursor = close - 1
                        while cursor >= 0 and text[cursor] == "\\":
                            slashes += 1
                            cursor -= 1
                        if slashes % 2 == 0:
                            break
                        close += 1

                    between = text[m.end() : close]
                    if not between.strip():
                        return True
                    if "," in m.group(1):
                        return False
                    return bool(re.search(r"\\[A-Za-z]+|[<>=+*/^_,{}-]", between))

                def _escape_currency(m: re.Match) -> str:
                    return m.group(0) if _looks_like_inline_math(m, p) else _rep_curr(m)

                # Split by backticks to avoid touching inline code or inline math $`...`$
                parts = re.split(r"(\$`[^`]*`\$|`[^`]*`)", modified_line)
                line_fixed = False
                for p_idx in range(0, len(parts), 2):
                    p = parts[p_idx]
                    if "$" in p:
                        new_p = self.CURRENCY_RE.sub(_escape_currency, p)
                        if new_p != p:
                            parts[p_idx] = new_p
                            line_fixed = True
                if line_fixed:
                    new_val = "".join(parts)
                    issues.append(
                        MathIssue(
                            file_path=file_path,
                            line_number=line_no,
                            rule="unescaped-currency-symbol",
                            description="Escaped monetary currency $ to prevent inline math parsing confusion.",
                            original=modified_line,
                            fixed=new_val,
                        )
                    )
                    modified_line = new_val

            if not in_code_block:
                new_val, repaired_rules = self.repair_markdown_line(
                    modified_line, in_math_block
                )
                if new_val != modified_line:
                    for rule in sorted(repaired_rules):
                        issues.append(
                            MathIssue(
                                file_path=file_path,
                                line_number=line_no,
                                rule=rule,
                                description=f"Repaired the {rule.replace('-', ' ')}.",
                                original=modified_line,
                                fixed=new_val,
                            )
                        )
                    modified_line = new_val

            new_lines.append(modified_line)
            idx += 1

        fixed_content = "".join(new_lines)
        return issues, fixed_content

    def fix_file(self, file_path: Path, fixed_content: str) -> None:
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(fixed_content)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Audit and automatically fix KaTeX / Markdown math syntax issues."
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
        help="Automatically fix math syntax issues in-place.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="CI mode: exit with code 1 if any issues are detected, 0 otherwise.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Preview changes without modifying files.",
    )
    parser.add_argument(
        "--diff",
        action="store_true",
        help="Show unified diff of proposed fixes.",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Print detailed issue information.",
    )

    args = parser.parse_args()
    root_dir = args.root.resolve()
    target_path = args.path or root_dir
    if not target_path.is_absolute():
        target_path = root_dir / target_path
    target_path = target_path.resolve()

    if target_path.is_file():
        md_files = [target_path] if target_path.suffix == ".md" else []
    else:
        md_files = [
            p
            for p in target_path.glob("**/*.md")
            if not any(part in p.parts for part in [".lake", ".git", "scripts"])
        ]

    print(f"[*] Scanning {len(md_files)} Markdown files for KaTeX math syntax issues...\n")
    fixer = MarkdownMathFixer(root_dir)

    total_issues = 0
    files_with_issues: List[Tuple[Path, List[MathIssue], str]] = []

    for md_file in sorted(md_files):
        issues, fixed_content = fixer.audit_file(md_file)
        if issues:
            total_issues += len(issues)
            files_with_issues.append((md_file, issues, fixed_content))
            rel_file = md_file.relative_to(root_dir).as_posix()
            print(f"📄 {rel_file}: {len(issues)} math issue(s) detected:")
            for issue in issues:
                print(f"   Line {issue.line_number} [{issue.rule}]: {issue.description}")
                if args.verbose or args.dry_run:
                    print(f"     Original: {repr(issue.original.strip())}")
                    print(f"     Fixed:    {repr(issue.fixed.strip())}")

            if args.diff:
                with open(md_file, "r", encoding="utf-8") as f:
                    orig_content = f.read()
                diff = difflib.unified_diff(
                    orig_content.splitlines(),
                    fixed_content.splitlines(),
                    fromfile=f"a/{rel_file}",
                    tofile=f"b/{rel_file}",
                    lineterm="",
                )
                print("\n".join(diff) + "\n")

    print("\n" + "=" * 60)
    print(f"Math Audit Summary: {total_issues} issue(s) found in {len(files_with_issues)} file(s).")
    print("=" * 60)

    if args.fix:
        if args.dry_run:
            print("[!] Dry-run enabled: No files were modified.")
        else:
            print("[*] Applying automatic math syntax fixes to Markdown files...")
            for md_file, issues, fixed_content in files_with_issues:
                fixer.fix_file(md_file, fixed_content)
                rel_file = md_file.relative_to(root_dir).as_posix()
                print(f"[✓] Fixed {len(issues)} issue(s) in {rel_file}")
            print("[✓] All math syntax issues fixed successfully.")

    if args.check:
        if total_issues > 0:
            print(f"[✗] Check failed: {total_issues} math syntax issues detected.")
            return 1
        print("[✓] Check passed: All Markdown math syntax is clean.")
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
