#!/usr/bin/env python3
"""Check Markdown math for common structural and KaTeX syntax errors.

This is a read-only companion to ``fix_markdown_math.py``. It checks fenced
math and inline math without attempting to rewrite the source.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class MathIssue:
    path: Path
    line: int
    rule: str
    message: str


FENCE_OPEN_RE = re.compile(r"^(\s*)(`{3,}|~{3,})(.*)$")
ENV_RE = re.compile(r"\\(begin|end)\s*\{([^{}]+)\}")
MATH_ONLY_COMMAND_RE = re.compile(
    r"\\(triangleright|succ|mathsf|mathcal|mathrm|mathbb|mathit|mathbf|mathfrak|mathscr|"
    r"mathrel|mathbin|mathop|mathord|mathopen|mathclose|mathinner|setminus|subseteq|"
    r"subsetneq|supseteq|supsetneq|cup|cap|times|cdot|forall|exists|in|notin|wedge|"
    r"vee|neg|implies|iff|prec|preceq|succeq|le|leq|ge|geq|neq|equiv|to|mapsto|"
    r"colon|emptyset|varnothing|infty|min|max|lim|sup|inf|sum|prod|int|partial|nabla|"
    r"ldots|cdots|dots|alpha|beta|gamma|delta|epsilon|varepsilon|theta|lambda|mu|nu|"
    r"xi|pi|rho|sigma|tau|phi|varphi|psi|omega|Gamma|Delta|Theta|Lambda|Pi|Sigma|"
    r"Phi|Psi|Omega)(?![A-Za-z])"
)
MISSING_SUPERSCRIPT_RE = re.compile(r"\^(?:\{\s*(?:_\s*)?\}|(?=\s|_|}|$))")
STAR_SUPERSCRIPT_RE = re.compile(r"(?<!\\)\^(?:\*|\{[^{}]*\*+[^{}]*\})")
UNSPACED_RELATIONAL_OPERATOR_RE = re.compile(
    r"(?<=[A-Za-z0-9_\})])[<>][A-Za-z]|(?<=[ \t])[<>][A-Za-z]|(?<=[A-Za-z0-9_\})])[<>](?=[ \t])"
)
UNESCAPED_DELIMITER_BRACE_RE = re.compile(
    r"\\(left|right|middle)\s*(\\)?([{}])"
)
UNBRACED_PAREN_SUPERSCRIPT_RE = re.compile(r"\^_\s*(?P<group>\([^()\n]*\))")
OVERESCAPED_PROOF_SYMBOL_RE = re.compile(r"\\\\(square|blacksquare)\b")
CORRUPTED_TEXT_COMMAND_RE = re.compile(r"\text\{")
UNSUBSCRIPTED_MATHCAL_TEXT_RE = re.compile(
    r"(\\mathcal\s*\{[^{}]+\})\s*\{\s*\\text\s*\{([^{}]+)\}\s*\}"
)
ALIGNED_ROW_SEPARATOR_RE = re.compile(r"(?<!\\)\\[ \t]+&")
ALIGNED_SINGLE_ROW_BREAK_RE = re.compile(r"(?<!\\)\\[ \t]*\r?\n[ \t]*&")
LIST_ITEM_RE = re.compile(r"^(?P<indent> *)(?P<marker>[-+*]|\d+[.)])(?P<gap> +)")
INLINE_BACKTICK_MATH_RE = re.compile(r"(?<!\\)\$`([^`\n]*)`\$")
INLINE_BACKTICK_START_RE = re.compile(r"(?<!\\)\$`")
INLINE_DOLLAR_MATH_RE = re.compile(
    r"(?<!\\)(?<!\$)\$(?!\$)(?:\\.|[^$\n])+?(?<!\\)(?<!\$)\$(?!\$)"
)
QUOTED_INLINE_DISPLAY_RE = re.compile(
    r"^[ \t]*(?P<quote>[\"'])\$\$.*?\$\$(?P=quote)[ \t]*$"
)
VULNERABLE_INLINE_MATH_PUNCT_RE = re.compile(r"[^a-zA-Z0-9\\][ \t]*_")
PARENTHESIZED_INLINE_MATH_RE = re.compile(
    r"(\(\$(?![$\`])[^\n$]*\([^\n$]*\)[^\n$]*?(?<!\\)\$|"
    r"(?<!\\)\$(?![$\`])[^\n$]*\([^\n$]*\)[^\n$]*?(?<!\\)\$\)|"
    r"\([^()\n$]+(?<!\\)\$(?![$\`])[^$\n]+?(?<!\\)\$\))"
)
MATRIX_ENV_RE = re.compile(
    r"\\begin\s*\{(?P<env>(?:p|b|B|v|V)?matrix|cases|array)\}(?:\{[^{}]*\})?(?P<body>.*?)\\end\s*\{(?P=env)\}",
    re.DOTALL,
)
MISSING_APOSTROPHE_RULES = (
    (re.compile(r"\bagent s\b"), "agent's"),
    (re.compile(r"\bRicardo s\b"), "Ricardo's"),
    (re.compile(r"\bmodel s\b"), "model's"),
    (re.compile(r"\bseller s\b"), "seller's"),
    (re.compile(r"\bB\s+hm-Bawerk\b"), "Böhm-Bawerk"),
)


def tex_atom_end(source: str, start: int) -> int | None:
    """Return the end of one TeX atom, including a balanced braced group."""
    while start < len(source) and source[start].isspace():
        start += 1
    if start >= len(source):
        return None
    if source[start] == "{":
        depth = 1
        cursor = start + 1
        while cursor < len(source):
            if not is_escaped(source, cursor):
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


def double_subscript_positions(source: str) -> list[int]:
    """Find a second subscript attached to the same TeX base atom."""
    positions: list[int] = []
    cursor = 0
    while cursor < len(source):
        if source[cursor] != "_" or is_escaped(source, cursor):
            cursor += 1
            continue
        first_end = tex_atom_end(source, cursor + 1)
        if first_end is None:
            cursor += 1
            continue
        second_start = first_end
        while second_start < len(source) and source[second_start].isspace():
            second_start += 1
        if second_start < len(source) and source[second_start] == "_" and not is_escaped(source, second_start):
            positions.append(second_start)
            second_end = tex_atom_end(source, second_start + 1)
            cursor = second_end if second_end is not None else second_start + 1
        else:
            cursor = first_end
    return positions


def code_span_ranges(text: str) -> list[tuple[int, int]]:
    """Return inline-code ranges, matching Markdown's exact backtick runs."""
    ranges: list[tuple[int, int]] = []
    index = 0
    while index < len(text):
        if text[index] != "`":
            index += 1
            continue
        run_end = index
        while run_end < len(text) and text[run_end] == "`":
            run_end += 1
        run_length = run_end - index
        # A backtick immediately following `$` is the opening mark in this
        # repository's inline-math syntax, not an inline-code opener.
        if index > 0 and text[index - 1] == "$":
            index = run_end
            continue
        search = run_end
        closing: tuple[int, int] | None = None
        while search < len(text):
            candidate = text.find("`", search)
            if candidate < 0:
                break
            candidate_end = candidate
            while candidate_end < len(text) and text[candidate_end] == "`":
                candidate_end += 1
            if candidate_end - candidate == run_length:
                closing = (candidate, candidate_end)
                break
            search = candidate_end
        if closing is None:
            index = run_end
        else:
            ranges.append((index, closing[1]))
            index = closing[1]
    return ranges


def is_escaped(text: str, index: int) -> bool:
    """Return whether the character at index is preceded by an odd slash run."""
    slashes = 0
    index -= 1
    while index >= 0 and text[index] == "\\":
        slashes += 1
        index -= 1
    return slashes % 2 == 1


def mask_ranges(text: str, ranges: Iterable[tuple[int, int]]) -> str:
    chars = list(text)
    for start, end in ranges:
        for index in range(start, end):
            if chars[index] != "\n":
                chars[index] = " "
    return "".join(chars)


def line_math_ranges(line: str) -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    """Find inline math and code spans on one line, preserving source offsets."""
    math_ranges = [match.span() for match in INLINE_BACKTICK_MATH_RE.finditer(line)]
    without_math = mask_ranges(line, math_ranges)
    code_ranges = code_span_ranges(without_math)
    masked = mask_ranges(without_math, code_ranges)
    math_ranges.extend(match.span() for match in INLINE_DOLLAR_MATH_RE.finditer(masked))
    return math_ranges, code_ranges


def emphasis_markers_around_inline_math(line: str) -> list[tuple[int, int]]:
    """Return emphasis marker ranges whose spans enclose inline math."""
    math_ranges, code_ranges = line_math_ranges(line)
    if not math_ranges:
        return []

    masked = mask_ranges(line, [*math_ranges, *code_ranges])
    emphasis_tokens = re.finditer(r"(?<!\\)\*{1,3}", masked)
    openings: list[tuple[str, int]] = []
    emphasis_ranges: list[tuple[int, int, str, int]] = []
    for token in emphasis_tokens:
        marker = token.group()
        if len(marker) == 3:
            continue
        start, end = token.span()
        before = masked[start - 1] if start > 0 else " "
        after = masked[end] if end < len(masked) else " "
        can_close = not before.isspace()
        can_open = not after.isspace()

        if openings and openings[-1][0] == marker and can_close:
            _, opening = openings.pop()
            emphasis_ranges.append((opening, end, marker, start))
        elif can_open:
            openings.append((marker, start))

    marker_ranges: set[tuple[int, int]] = set()
    for opening, closing, marker, closing_start in emphasis_ranges:
        if any(opening < math_start and math_end < closing for math_start, math_end in math_ranges):
            marker_ranges.add((opening, opening + len(marker)))
            marker_ranges.add((closing_start, closing))
    return sorted(marker_ranges)


def inspect_tex(
    source: str,
    path: Path,
    first_line: int,
    issues: list[MathIssue],
    markdown_inline: bool = False,
) -> None:
    """Check balancing and a few common KaTeX structural errors in math."""
    braces: list[tuple[int, int]] = []
    environments: list[tuple[str, int]] = []
    left_right: list[int] = []

    for offset in double_subscript_positions(source):
        line_offset = source.count("\n", 0, offset)
        issues.append(
            MathIssue(
                path,
                first_line + line_offset,
                "double-subscript",
                "A TeX atom has two adjacent subscripts; combine them in one braced subscript, such as `x_{i,j}`.",
            )
        )

    for match in STAR_SUPERSCRIPT_RE.finditer(source):
        line_offset = source.count("\n", 0, match.start())
        issues.append(
            MathIssue(
                path,
                first_line + line_offset,
                "unbraced-star-superscript",
                "A bare `*` superscript can be parsed as Markdown emphasis; write it as `^{\\ast}`.",
            )
        )

    for match in UNSPACED_RELATIONAL_OPERATOR_RE.finditer(source):
        line_offset = source.count("\n", 0, match.start())
        issues.append(
            MathIssue(
                path,
                first_line + line_offset,
                "unspaced-relational-operator",
                "Binary relational operators `<` and `>` should be padded with spaces (e.g. `s < t` instead of `s<t`) to avoid collision with HTML tag syntax.",
            )
        )

    for match in UNESCAPED_DELIMITER_BRACE_RE.finditer(source):
        if is_escaped(source, match.start()):
            continue
        line_offset = source.count("\n", 0, match.start())
        cmd = match.group(1)
        brace = match.group(3)
        issues.append(
            MathIssue(
                path,
                first_line + line_offset,
                "unescaped-delimiter-brace",
                f"Delimiter brace `{brace}` for `\\{cmd}` must be written as `\\{cmd}\\lbrace` or `\\{cmd}\\rbrace` to prevent GitHub CommonMark from stripping the brace escape.",
            )
        )

    for line_offset, line in enumerate(source.splitlines() or [source]):
        if CORRUPTED_TEXT_COMMAND_RE.search(line):
            issues.append(
                MathIssue(
                    path,
                    first_line + line_offset,
                    "corrupted-text-command",
                    "A tab has replaced the start of `\\text{...}`; restore the TeX command.",
                )
            )
        for match in OVERESCAPED_PROOF_SYMBOL_RE.finditer(line):
            issues.append(
                MathIssue(
                    path,
                    first_line + line_offset,
                    "overescaped-proof-symbol",
                    f"`\\\\{match.group(1)}` has an extra backslash inside math; use `\\{match.group(1)}`.",
                )
            )
        for index, char in enumerate(line):
            if is_escaped(line, index):
                continue
            if char == "{":
                braces.append((index, first_line + line_offset))
            elif char == "}":
                if braces:
                    braces.pop()
                else:
                    issues.append(
                        MathIssue(path, first_line + line_offset, "unmatched-brace", "Closing `}` has no matching opening `{`.")
                    )

        unbraced_parenthesized = {
            match.start()
            for match in UNBRACED_PAREN_SUPERSCRIPT_RE.finditer(line)
            if not is_escaped(line, match.start())
        }
        for _offset in sorted(unbraced_parenthesized):
            issues.append(
                MathIssue(
                    path,
                    first_line + line_offset,
                    "missing-open-brace-superscript",
                    "A parenthesized superscript after `^_` needs braces, such as `S^{(k_1)}`.",
                )
            )

        for match in MISSING_SUPERSCRIPT_RE.finditer(line):
            if not is_escaped(line, match.start()):
                if match.start() in unbraced_parenthesized:
                    continue
                issues.append(
                    MathIssue(
                        path,
                        first_line + line_offset,
                        "missing-superscript-argument",
                        "A superscript marker `^` must be followed by a math atom or a braced expression.",
                    )
                )

        line_number = first_line + line_offset
        events = [
            (match.start(), "environment", match)
            for match in ENV_RE.finditer(line)
            if not is_escaped(line, match.start())
        ]
        events.extend(
            (match.start(), "hline", match)
            for match in re.finditer(r"\\hline\b", line)
            if not is_escaped(line, match.start())
        )
        for _, event_type, match in sorted(events, key=lambda event: event[0]):
            if event_type == "hline":
                # \hline is an array row separator in KaTeX; outside an array
                # it commonly causes the renderer's "Misplaced \\hline" error.
                if not any(name == "array" for name, _ in environments):
                    issues.append(
                        MathIssue(path, line_number, "misplaced-hline", "`\\hline` must appear inside an `array` environment.")
                    )
                continue

            kind, name = match.groups()
            if kind == "begin":
                environments.append((name, line_number))
                if name == "array":
                    after = line[match.end() :]
                    if not re.match(r"\s*\{[^{}]*\}", after):
                        issues.append(
                            MathIssue(path, line_number, "array-column-spec", "`array` needs a column specification, for example `\\begin{array}{lr}`.")
                        )
            elif environments and environments[-1][0] == name:
                environments.pop()
            elif environments:
                issues.append(
                    MathIssue(path, line_number, "mismatched-environment", f"`\\end{{{name}}}` closes an environment while `{environments[-1][0]}` is still open.")
                )
            else:
                issues.append(
                    MathIssue(path, line_number, "unmatched-environment", f"`\\end{{{name}}}` has no matching `\\begin{{{name}}}`.")
                )

        for match in re.finditer(r"\\(left|right)\b", line):
            if is_escaped(line, match.start()):
                continue
            command = match.group(1)
            line_number = first_line + line_offset
            if command == "left":
                left_right.append(line_number)
            elif left_right:
                left_right.pop()
            else:
                issues.append(
                    MathIssue(path, line_number, "unmatched-right", "`\\right` has no matching `\\left`.")
                )

        if any(not is_escaped(line, match.start()) for match in re.finditer(r"\\operatorname\*?\b", line)):
            issues.append(
                MathIssue(path, first_line + line_offset, "disallowed-operatorname", "GitHub KaTeX disallows `\\operatorname`; use a supported notation such as `\\text{...}`.")
            )

        if UNSUBSCRIPTED_MATHCAL_TEXT_RE.search(line):
            issues.append(
                MathIssue(
                    path,
                    first_line + line_offset,
                    "missing-set-label-subscript",
                    "A text label following a calligraphic set symbol needs a subscript, for example `\\mathcal{A}_{\\text{feas}}`.",
                )
            )

    if re.search(r"\\begin\s*\{aligned\}", source):
        malformed_separator = ALIGNED_ROW_SEPARATOR_RE.search(source)
        malformed_line_break = ALIGNED_SINGLE_ROW_BREAK_RE.search(source)
        match = malformed_separator or malformed_line_break
        if match:
            line_offset = source.count("\n", 0, match.start())
            issues.append(
                MathIssue(
                    path,
                    first_line + line_offset,
                    "malformed-aligned-row-separator",
                    "Use `\\\\` to end the aligned row before the next row's `&`.",
                )
            )

    for match in MATRIX_ENV_RE.finditer(source):
        body = match.group("body")
        for malformed in re.finditer(r"(?<!\\)\\[ \t]*\r?\n|(?<!\\)\\[ \t]+", body):
            line_offset = source.count("\n", 0, match.start("body") + malformed.start())
            issues.append(
                MathIssue(
                    path,
                    first_line + line_offset,
                    "malformed-matrix-row-separator",
                    "Use `\\\\` for row breaks inside matrix and cases environments.",
                )
            )

    for line_offset, line in enumerate(source.splitlines()):
        for text_match in re.finditer(r"\\text\s*\{", line):
            opening = text_match.end() - 1
            depth = 1
            cursor = opening + 1
            while cursor < len(line) and depth:
                if not is_escaped(line, cursor):
                    if line[cursor] == "{":
                        depth += 1
                    elif line[cursor] == "}":
                        depth -= 1
                cursor += 1
            text_content = line[opening + 1 : cursor - 1] if depth == 0 else ""
            math_command = MATH_ONLY_COMMAND_RE.search(text_content)
            if math_command:
                command = math_command.group(1)
                issues.append(
                    MathIssue(
                        path,
                        first_line + line_offset,
                        "math-command-in-text",
                        f"\\{command} must be outside \\text{{...}} because it is a math-mode command.",
                    )
                )
            if re.search(r"\\?&", text_content):
                issues.append(
                    MathIssue(
                        path,
                        first_line + line_offset,
                        "ampersand-in-text",
                        "KaTeX disallows `&` or `\\&` inside `\\text{...}`; replace with words or letters such as `\\text{RD}`.",
                    )
                )

    for _, line_number in braces:
        issues.append(MathIssue(path, line_number, "unmatched-brace", "Opening `{` has no matching closing `}`."))
    for name, line_number in environments:
        issues.append(
            MathIssue(path, line_number, "unclosed-environment", f"`\\begin{{{name}}}` has no matching `\\end{{{name}}}`.")
        )
    for line_number in left_right:
        issues.append(MathIssue(path, line_number, "unmatched-left", "`\\left` has no matching `\\right`."))


def is_vulnerable_inline_math(body: str) -> bool:
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
    return bool(VULNERABLE_INLINE_MATH_PUNCT_RE.search(body))


def inspect_inline_line(line: str, path: Path, line_number: int, issues: list[MathIssue]) -> None:
    """Extract inline math while ignoring inline code and validate delimiters."""
    if emphasis_markers_around_inline_math(line):
        issues.append(
            MathIssue(
                path,
                line_number,
                "inline-math-in-emphasis",
                "Remove Markdown emphasis around inline math; some Markdown/KaTeX renderers fail to render math nested in emphasis.",
            )
        )

    for match in PARENTHESIZED_INLINE_MATH_RE.finditer(line):
        issues.append(
            MathIssue(
                path,
                line_number,
                "parenthesized-inline-math",
                "Inline math adjacent to parentheses with internal parentheses fails to render on GitHub; use `( $...$ )` or pad with spaces.",
            )
        )

    prose_math_ranges, prose_code_ranges = line_math_ranges(line)
    prose_only = mask_ranges(line, [*prose_math_ranges, *prose_code_ranges])

    if r"\$" in prose_only and re.search(r"\\\$[0-9]", prose_only):
        if prose_math_ranges:
            issues.append(
                MathIssue(
                    path,
                    line_number,
                    "currency-math-collision",
                    "Escaped currency sign `\\$` shares a line with inline math `$...$`. On GitHub, CommonMark unescapes `\\$` to `$`, which pairs with math delimiters and turns prose into broken math. Write currency with 'USD' or plain numbers.",
                )
            )
        elif line.strip().startswith("|"):
            issues.append(
                MathIssue(
                    path,
                    line_number,
                    "currency-table-collision",
                    "Escaped currency sign `\\$` in table row can pair across cells when CommonMark unescapes `\\$` to `$`. Write currency in table header and use plain numbers in cells.",
                )
            )
    for match in MATH_ONLY_COMMAND_RE.finditer(prose_only):
        issues.append(
            MathIssue(
                path,
                line_number,
                "math-command-outside-math",
                f"`\\{match.group(1)}` appears outside math delimiters; wrap the symbol in `$...$`.",
            )
        )
    for pattern, replacement in MISSING_APOSTROPHE_RULES:
        for _match in pattern.finditer(prose_only):
            issues.append(
                MathIssue(
                    path,
                    line_number,
                    "missing-apostrophe-or-character",
                    f"Restore the missing character in this prose (expected `{replacement}`).",
                )
            )

    math_ranges: list[tuple[int, int]] = []
    for match in INLINE_BACKTICK_MATH_RE.finditer(line):
        inspect_tex(match.group(1), path, line_number, issues)
        math_ranges.append(match.span())

    without_math = mask_ranges(line, math_ranges)
    code_ranges = code_span_ranges(without_math)
    masked = mask_ranges(without_math, code_ranges)

    if re.search(r"(?<!\\)\$\$", masked):
        message = "Display-math delimiters `$$` must appear on their own lines."
        if QUOTED_INLINE_DISPLAY_RE.match(masked):
            message += " Remove quotation marks around a complete display equation."
        issues.append(
            MathIssue(
                path,
                line_number,
                "inline-display-math",
                message,
            )
        )

    # A `$` followed by a backtick is the repository's preferred inline math
    # opener. Diagnose it explicitly when its closing backtick-dollar is absent.
    malformed_starts: list[tuple[int, int]] = []
    for match in INLINE_BACKTICK_START_RE.finditer(masked):
        if match.start() < len(masked) and masked[match.start()] == "$":
            issues.append(
                MathIssue(path, line_number, "unclosed-inline-math", "Inline math opened with `$` followed by a backtick is missing its closing backtick-dollar delimiter.")
            )
            malformed_starts.append(match.span())
    masked = mask_ranges(masked, malformed_starts)

    # Check ordinary $...$ and $$...$$ delimiters too. Escaped currency signs,
    # dollar amounts such as $50, code spans, and the backtick-dollar form
    # handled above are not considered math delimiters here.
    dollar_tokens: list[tuple[int, int]] = []

    def numeric_dollar_starts_math(start: int) -> bool:
        """Distinguish a numeric inline-math opener from a currency sign."""
        close = start + 1
        while close < len(masked):
            close = masked.find("$", close)
            if close < 0:
                return False
            if not is_escaped(masked, close):
                break
            close += 1

        contents = masked[start + 1 : close]
        if re.fullmatch(r"\d+(?:\.\d+)?", contents.strip()):
            return True
        if not contents.strip():
            return True
        return bool(re.search(r"\\[A-Za-z]+|[<>=+*/^_,{}-]", contents))

    index = 0
    while index < len(masked):
        if masked[index] != "$" or is_escaped(masked, index):
            index += 1
            continue
        if index + 1 < len(masked) and masked[index + 1] == "`":
            index += 2
            continue
        if index and masked[index - 1] == "`":
            index += 1
            continue
        if index + 1 < len(masked) and masked[index + 1] == "$":
            dollar_tokens.append((index, index + 2))
            index += 2
            continue
        if index + 1 < len(masked) and masked[index + 1].isdigit():
            if not numeric_dollar_starts_math(index):
                index += 1
                continue
        dollar_tokens.append((index, index + 1))
        index += 1

    pending: tuple[int, int] | None = None
    for token in dollar_tokens:
        if pending is None:
            pending = token
            continue
        start, end = pending
        close_start, close_end = token
        is_inline_pair = end - start == 1 and close_end - close_start == 1
        body = masked[end:close_start]
        if is_inline_pair and is_vulnerable_inline_math(body):
            issues.append(
                MathIssue(
                    path,
                    line_number,
                    "unprotected-inline-math",
                    "Inline math containing escaped braces `\\{...\\}`, `\\_`, `\\$`, `\\\\`, matrix environments, or non-alphanumeric subscripts must use backtick delimiters `$`...`$` to prevent CommonMark from corrupting the TeX source.",
                )
            )
        inspect_tex(
            body,
            path,
            line_number,
            issues,
            markdown_inline=is_inline_pair,
        )
        pending = None
    if pending is not None:
        issues.append(
            MathIssue(path, line_number, "unclosed-dollar-math", "Math delimiter `$` or `$$` has no matching closing delimiter on this line.")
        )


def check_file(path: Path) -> list[MathIssue]:
    issues: list[MathIssue] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as error:
        return [MathIssue(path, 1, "read-error", f"Could not read file: {error}")]

    fence_char: str | None = None
    fence_length = 0
    fence_is_math = False
    fence_line = 0
    math_lines: list[str] = []
    display_math_line: int | None = None
    display_math_lines: list[str] = []

    for line_number, line in enumerate(lines, start=1):
        fence_match = FENCE_OPEN_RE.match(line)
        if fence_char is None:
            if display_math_line is not None:
                if line.strip() == "$$":
                    inspect_tex("\n".join(display_math_lines), path, display_math_line + 1, issues)
                    display_math_line = None
                    display_math_lines = []
                else:
                    display_math_lines.append(line)
                continue
            if line.strip() == "$$":
                math_indent = len(line) - len(line.lstrip(" "))
                if math_indent > 0:
                    in_list = False
                    previous = line_number - 2
                    while previous >= 0:
                        prev_line = lines[previous]
                        if not prev_line.strip():
                            previous -= 1
                            continue
                        if LIST_ITEM_RE.match(prev_line):
                            in_list = True
                            break
                        if not prev_line.startswith(" ") and not prev_line.startswith("\t"):
                            break
                        previous -= 1

                    issues.append(
                        MathIssue(
                            path,
                            line_number,
                            "display-math-in-list-item" if in_list else "indented-display-math",
                            "Display math nested in a list may not render consistently; move it outside the list or use inline math."
                            if in_list
                            else "A display-math delimiter `$$` must start at column 1 to render consistently.",
                        )
                    )
                display_math_line = line_number
                display_math_lines = []
                continue
            if fence_match:
                indent, fence, info = fence_match.groups()
                info_word = info.strip().split(maxsplit=1)[0] if info.strip() else ""
                fence_char = fence[0]
                fence_length = len(fence)
                fence_is_math = info_word == "math"
                fence_line = line_number
                math_lines = []
                if fence_is_math and indent:
                    issues.append(
                        MathIssue(path, line_number, "indented-math-fence", "A display-math fence must start at column 1 to render consistently.")
                    )
                continue
            leading_spaces = len(line) - len(line.lstrip(" "))
            if leading_spaces >= 4 and "$" in line and not LIST_ITEM_RE.match(line.lstrip()):
                issues.append(
                    MathIssue(
                        path,
                        line_number,
                        "indented-prose-math",
                        f"Prose line with inline math is indented by {leading_spaces} spaces; GitHub will parse it as a preformatted code block rather than rendering math. Reduce indentation to 3 or fewer spaces.",
                    )
                )
            inspect_inline_line(line, path, line_number, issues)
            continue

        close_match = re.match(r"^\s*(`+|~+)\s*$", line)
        is_closer = bool(
            close_match
            and close_match.group(1)[0] == fence_char
            and len(close_match.group(1)) >= fence_length
        )
        if is_closer:
            if fence_is_math:
                inspect_tex("\n".join(math_lines), path, fence_line + 1, issues)
            fence_char = None
            fence_length = 0
            fence_is_math = False
            continue
        if fence_is_math:
            math_lines.append(line)

    if fence_char is not None and fence_is_math:
        issues.append(MathIssue(path, fence_line, "unclosed-math-fence", "Display-math fence has no matching closing fence."))
        inspect_tex("\n".join(math_lines), path, fence_line + 1, issues)
    if display_math_line is not None:
        issues.append(MathIssue(path, display_math_line, "unclosed-dollar-display-math", "Display math opened with `$$` has no matching closing `$$` delimiter."))
        inspect_tex("\n".join(display_math_lines), path, display_math_line + 1, issues)
    return issues


def markdown_files(target: Path) -> list[Path]:
    if target.is_file():
        return [target] if target.suffix.lower() == ".md" else []
    ignored = {".git", ".lake", "node_modules", ".venv", "venv"}
    return sorted(
        path
        for path in target.rglob("*.md")
        if not any(part in ignored or part.startswith(".") for part in path.relative_to(target).parts[:-1])
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Read-only structural checker for Markdown math syntax.")
    parser.add_argument("--root", type=Path, default=Path("."), help="Repository root (default: current directory).")
    parser.add_argument("--path", type=Path, help="Markdown file or directory to inspect (default: repository root).")
    args = parser.parse_args()

    root = args.root.resolve()
    target = (args.path if args.path is not None else root)
    if not target.is_absolute():
        target = root / target
    target = target.resolve()
    if not target.exists():
        print(f"error: path does not exist: {target}", file=sys.stderr)
        return 2

    files = markdown_files(target)
    if not files:
        print(f"No Markdown files found at {target}")
        return 0

    issues = [issue for file_path in files for issue in check_file(file_path)]
    for issue in issues:
        try:
            display_path = issue.path.relative_to(root)
        except ValueError:
            display_path = issue.path
        print(f"{display_path}:{issue.line}: [{issue.rule}] {issue.message}")

    if issues:
        print(f"Found {len(issues)} math syntax issue(s) in {len(files)} Markdown file(s).")
        return 1
    print(f"Math syntax looks structurally sound in {len(files)} Markdown file(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
