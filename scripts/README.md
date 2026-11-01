# Praxeology Lean Documentation Maintenance Scripts

This directory contains standalone Python maintenance utilities designed to ensure that the repository's Markdown specifications, critique essays, and documentation remain synchronized with the Lean 4 formalization and render cleanly across GitHub and KaTeX environments.

---

## 1. `update_theorem_links.py`

### Purpose
Audits Markdown files for references to Lean 4 source files (`.lean`), indexing all Lean declarations (theorems, definitions, lemmas, classes, structures, abbreviations, inductive types, and structure fields). It automatically identifies outdated line numbers (`#L...`), symbols that moved between Lean source files, and links missing anchor lines.

### Features
- **Lean 4 Source Indexer**: Dynamically parses all `.lean` files in `Praxeology/` (and root `Praxeology.lean`), tracking 1,100+ declarations and their exact line numbers.
- **Line Drift & Moved Symbol Detection**: Flags when Lean code edits shift line positions or when a declaration is refactored into a different file.
- **Smart Link Parser**: Resolves backticked identifiers (`[`foo`](...#L12)`), direct Lean names, and surrounding contextual identifiers while safely ignoring whole-file paths.
- **In-Place Auto-Fixing**: Automatically rewrites outdated URLs and anchors directly in Markdown documents.
- **CI / Gatekeeper Mode**: Returns exit code `1` if any outdated links are detected, and `0` when all links are up to date.

### Command-Line Options
| Option | Description |
|---|---|
| `--check` | CI mode: exits with `0` if all links are valid, `1` if any are outdated. |
| `--fix` | Automatically patches outdated links in-place across all targeted Markdown files. |
| `--dry-run` | Previews proposed link updates without modifying any files. |
| `--path <PATH>` | Audit a specific Markdown file or subdirectory (e.g. `--path critiques/critics_of_praxeology.md`). Defaults to entire repo. |
| `--root <DIR>` | Specifies repository root (defaults to `.`). |
| `--add-missing` | Adds `#L<line>` anchors to links that currently only point to `.lean` files without line numbers. |
| `-v`, `--verbose` | Displays detailed line-by-line before/after URL replacements. |

### Usage Examples
```bash
# Check if any theorem links in the repository are outdated (CI check)
python3 scripts/update_theorem_links.py --check

# Preview outdated links across all files without modifying them
python3 scripts/update_theorem_links.py --dry-run --verbose

# Automatically fix all outdated Lean links in-place
python3 scripts/update_theorem_links.py --fix

# Audit a single document
python3 scripts/update_theorem_links.py --path critiques/critics_of_praxeology.md
```

---

## 2. `fix_markdown_math.py`

### Purpose
Identifies and automatically repairs KaTeX and GitHub Flavored Markdown (GFM) math rendering errors across all documentation.

### Issues Detected & Resolved
1. **Disallowed KaTeX Macros (`\operatorname` / `\operatorname*`)**:
   - *Problem*: GitHub Flavored Markdown restricts KaTeX macros, throwing `"The following macros are not allowed: operatorname"`.
   - *Fix*: Automatically replaces `\operatorname{Name}` with standard, universally supported `\text{Name}` (e.g. `\text{Cov}(Z, \epsilon) = 0`).
2. **Hyphens in `\text{...}` Inside Math Blocks**:
   - *Problem*: Hyphens inside math mode `\text{functional-form}` are rendered as minus-sign glyphs or cause KaTeX font rendering artifacts.
   - *Fix*: Converts hyphens inside `\text{...}` to spaces (e.g. `\text{functional form}`), matching natural language standards.
3. **Indented Display Math Fences (````math`)**:
   - *Problem*: In Markdown lists, indented `   ```math` blocks are parsed by Markdown parsers as literal indented preformatted code blocks rather than block-level KaTeX display equations.
   - *Fix*: Normalizes ````math` blocks to start at column 0 with appropriate spacing.
4. **Unescaped Currency Signs (`$50`)**:
   - *Problem*: Raw currency signs followed by digits (e.g. `$50` or `$100 million`) inadvertently trigger inline math delimiter parsing (`$...$`), corrupting subsequent text.
   - *Fix*: Automatically escapes currency signs (`\$50`), preserving intended dollar amounts without interfering with inline math blocks (`$`...`$`).
5. **Unbraced Star Superscripts**:
   - *Problem*: A bare `*` in math such as `$m^*$` can be consumed by Markdown's emphasis parser before KaTeX renders the formula.
   - *Fix*: Replaces it with the TeX symbol `$m^{\ast}$`, so Markdown never sees a raw emphasis marker.
6. **Inline Display Math, List Math, and Malformed Set Labels**:
   - *Problem*: Same-line `$$...$$` delimiters do not form a display block; display math nested in lists may be ignored by some renderers; calligraphic set labels without a subscript attach at the baseline; and a single backslash before `&` does not start a new `aligned` row. Quotation marks around a complete same-line display also prevent it from being recognized as a display block.
   - *Fix*: Moves standalone display equations onto separate delimiter lines, moves list-level display math outside the list (or converts deeply nested list math to inline form), removes quotation marks around the equation, rewrites the set label as `\mathcal{A}_{\text{feas}}`, and changes the malformed aligned separator to a `\\` row break.
7. **Unprotected Inline Math with CommonMark Collisions**:
   - *Problem*: Inline formulas using single-dollar delimiters (`$...$`) that contain escaped braces (`\{...\}`), thin spaces (`\,`), escaped underscores (`\_`), or non-alphanumeric subscripts (such as `\mathcal{A}_{\text{feas}}` or `\mathsf{P}_{\mathrm{ex\text{-}ante},M}`) suffer character loss or emphasis pairing under CommonMark rules, stripping braces and underscores before KaTeX can render them.
   - *Fix*: Automatically wraps vulnerable inline formulas in GitHub-recommended backtick math delimiters (`$`...`$`) and pads parenthesized expressions (`( $`...`$ )`), preserving the exact TeX source.
8. **Unescaped Delimiter Braces (`\left{`, `\right}`, `\middle{`, `\middle}`)**:
   - *Problem*: Unescaped curly braces directly following `\left`, `\right`, or `\middle` trigger KaTeX syntax errors (`"Missing or unrecognized delimiter for \left"` or `"Missing or unrecognized delimiter for \right"`), because `{` and `}` are syntax grouping tokens in TeX rather than delimiter tokens.
   - *Fix*: Automatically escapes delimiter braces as `\left\{`, `\right\}`, `\middle\{`, or `\middle\}`, and ensures inline formulas are wrapped in backtick math delimiters so CommonMark does not strip the delimiter backslashes.

### Command-Line Options
| Option | Description |
|---|---|
| `--check` | CI mode: exits with `0` if all math formatting is clean, `1` if issues exist. |
| `--fix` | Automatically fixes math syntax issues in-place. |
| `--dry-run` | Previews changes without writing to disk. |
| `--diff` | Outputs a unified diff of all proposed syntax fixes. |
| `--path <PATH>` | Inspect a specific Markdown file or subdirectory. Defaults to entire repo. |
| `--root <DIR>` | Specifies repository root (defaults to `.`). |
| `-v`, `--verbose` | Prints detailed per-issue breakdown. |

### Usage Examples
```bash
# Check if any Markdown math formatting issues exist (CI check)
python3 scripts/fix_markdown_math.py --check

# View unified diff of proposed math fixes
python3 scripts/fix_markdown_math.py --diff

# Automatically fix all math formatting issues in-place
python3 scripts/fix_markdown_math.py --fix

# Inspect and fix a specific file
python3 scripts/fix_markdown_math.py --path spec/02_action_and_preference.md --fix
```

---

## 3. `check_markdown_math.py`

This read-only checker validates structural math syntax in Markdown without
changing files. It checks fenced display math and inline math while ignoring
ordinary code blocks and inline code examples. It reports file and line for
unclosed math fences or delimiters, display delimiters sharing a line with text,
display equations missing list-item spacing or indentation, empty or malformed
superscript arguments, unbalanced braces, mismatched LaTeX environments, unmatched
`\\left` / `\\right`, missing `array` column
specifications, misplaced `\\hline`, GitHub-disallowed `\\operatorname`, and
math-mode symbols such as `\\triangleright`, `\\succ`, `\\mathsf`, `\\mathcal`,
or `\\mathrm` placed inside `\\text{...}`, un-subscripted labels following a
calligraphic set symbol, unbraced star superscripts that Markdown can parse as
emphasis, unescaped delimiter braces (`\\left{`, `\\right}`, `\\middle{`, `\\middle}`),
and malformed row separators inside `aligned`. It also
reports inline formulas enclosed by Markdown emphasis, as well as single-dollar
inline formulas vulnerable to CommonMark emphasis collision or character stripping.
Use `fix_markdown_math.py` to repair supported formatting issues; the checker
itself remains read-only.

```bash
# Check all Markdown files
python3 scripts/check_markdown_math.py

# Check a specific document or directory
python3 scripts/check_markdown_math.py --path natural_language/08_price_signals_firms_and_intervention.md
```

The checker exits with `1` when it finds a math syntax issue, making it
suitable for CI.

---

## 4. `audit_adhoc_premises.py`

### Purpose
Audits the Lean 4 formalization for ad-hoc premise wrappers, exogenous macroeconomic shock structures, ungrounded subjective flips, and detached interaction payoff matrices.

### Checks Performed
1. **External Hypothesis Wrappers**:
   Flags any introduction of external hypothesis wrappers, exogenous rate shock structures, or ad-hoc factor starvation certificates.
2. **Ad-hoc Shock & Squeeze Declarations**:
   Heuristically flags new structures or classes declared as rate shocks, valuation signals, or completion squeezes.
3. **Ungrounded Subjective Flips**:
   Detects hypothesis signatures where an arithmetic comparison directly implies purposeful action without passing through teleological bundle dominance and the preference bridge.
4. **Detached Game Matrices**:
   Detects standalone payoff or outcome functions declared outside `ActionFrame` (e.g. `Outcome : Action → Action → Ends`), enforcing native multi-agent execution via `ActionFrame.jointBranch` and `ActionFrame.omega`.

```bash
# Check all Lean files for ad-hoc premises (CI gatekeeper)
python3 scripts/audit_adhoc_premises.py --check
```

---

## 5. `audit_axiomatic_floor.py`

Heuristic source-pattern screen for ontological leakage, `omit ... in` bypasses, shadow doxastic frames, and implicational bridge stuffing.

```bash
python3 scripts/audit_axiomatic_floor.py
```

---

## 6. Recommended CI / Pre-Commit Workflow

These tools are designed to run in continuous integration workflows (e.g. GitHub Actions) or as pre-commit hooks to prevent documentation regressions:

```yaml
# Example GitHub Actions step:
- name: Verify Documentation Links & Math
  run: |
    python3 scripts/update_theorem_links.py --check
    python3 scripts/fix_markdown_math.py --check
    python3 scripts/check_markdown_math.py
    python3 scripts/audit_adhoc_premises.py --check
    python3 scripts/audit_axiomatic_floor.py
```
