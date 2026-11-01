"""Regression tests for Markdown math formatting repairs."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_markdown_math import check_file  # noqa: E402
from fix_markdown_math import MarkdownMathFixer  # noqa: E402


class QuotedDisplayMathTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp_dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp_dir.cleanup)
        self.root = Path(self.temp_dir.name)
        self.path = self.root / "sample.md"
        self.fixer = MarkdownMathFixer(self.root)

    def test_physical_dominance_display_is_unquoted_and_reflowed(self) -> None:
        self.path.write_text(
            '"$$ \\triangleright_{\\mathrm{P}}(b_1, b_2) \\iff '
            '(\\forall m \\in \\mathcal{M}, b_2(m) \\le b_1(m)) '
            '\\wedge (\\exists m \\in \\mathcal{M}, b_2(m) < b_1(m)) $$"\n',
            encoding="utf-8",
        )

        issues, fixed = self.fixer.audit_file(self.path)

        self.assertIn("Moved same-line display math", issues[0].description)
        self.assertTrue(fixed.startswith("$$\n"))
        self.assertNotIn('"$$', fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_feasibility_display_repairs_set_subscripts(self) -> None:
        self.path.write_text(
            '"$$ \\alpha \\in \\mathcal{A}{\\text{feas}}(i, t, h) '
            '\\iff \\alpha \\in \\mathcal{A}{\\text{cont}}(i, t, h) '
            '\\wedge \\forall m \\in \\mathcal{M}, \\quad '
            'u(\\alpha, m) \\le \\omega(i, t, h, m) $$"\n',
            encoding="utf-8",
        )

        issues, fixed = self.fixer.audit_file(self.path)

        self.assertTrue(any(issue.rule == "missing-set-label-subscript" for issue in issues))
        self.assertIn(r"\mathcal{A}_{\text{feas}}", fixed)
        self.assertIn(r"\mathcal{A}_{\text{cont}}", fixed)
        self.assertNotIn('"$$', fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_inline_feasibility_formula_repairs_set_subscript(self) -> None:
        self.path.write_text(
            "The actions satisfy $\\alpha^{\\ast}, \\beta \\in "
            "\\mathcal{A}{\\text{feas}}(i, t, h)$ at this node.\n",
            encoding="utf-8",
        )

        issues, fixed = self.fixer.audit_file(self.path)

        self.assertTrue(any(issue.rule == "missing-set-label-subscript" for issue in issues))
        self.assertIn(r"\mathcal{A}_{\text{feas}}", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_checker_explains_quoted_single_line_display(self) -> None:
        self.path.write_text('"$$ x = y $$"\n', encoding="utf-8")

        issues = check_file(self.path)

        display_issue = next(issue for issue in issues if issue.rule == "inline-display-math")
        self.assertIn("Remove quotation marks", display_issue.message)

    def test_top_level_list_display_moves_outside_the_list(self) -> None:
        self.path.write_text(
            "1. This condition is written as:\n\n"
            "   $$\n   x = y\n   $$\n",
            encoding="utf-8",
        )

        issues, fixed = self.fixer.audit_file(self.path)

        self.assertTrue(any(issue.rule == "display-math-in-list-item" for issue in issues))
        self.assertIn("1. This condition is written as:\n\n$$\nx = y\n$$", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_nested_list_display_becomes_inline_math(self) -> None:
        self.path.write_text(
            "1. Outer item\n\n   - Inner condition:\n\n"
            "     $$\n     x = y\n     $$\n",
            encoding="utf-8",
        )

        issues, fixed = self.fixer.audit_file(self.path)

        self.assertTrue(any(issue.rule == "display-math-in-list-item" for issue in issues))
        self.assertIn("   - Inner condition: $x = y$", fixed)
        self.assertNotIn("$$", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_checker_flags_display_math_nested_in_list(self) -> None:
        self.path.write_text("1. Item:\n\n   $$\n   x = y\n   $$\n", encoding="utf-8")

        issues = check_file(self.path)

        self.assertTrue(any(issue.rule == "display-math-in-list-item" for issue in issues))

    def test_checker_flags_display_math_nested_in_list_continuation(self) -> None:
        self.path.write_text(
            "1. **The Rate of Profit Formula:**\n"
            "   Marx expressed the rate of profit as:\n"
            "   $$\n"
            "   r = \\frac{s}{c + v}\n"
            "   $$\n",
            encoding="utf-8",
        )

        issues = check_file(self.path)

        self.assertTrue(any(issue.rule == "display-math-in-list-item" for issue in issues))

    def test_double_subscripts_are_grouped_in_one_subscript(self) -> None:
        self.path.write_text(
            "$$\n"
            r"\mathsf{P}_{\mathrm{dox}}_M(i,t,H_t,h)\quad"
            r"\mathsf{P}_{\mathrm{ex\text{-}ante}}_M(i,t,h,\alpha)"
            "\n$$\n",
            encoding="utf-8",
        )

        issues = check_file(self.path)
        self.assertEqual(sum(issue.rule == "double-subscript" for issue in issues), 2)

        fix_issues, fixed = self.fixer.audit_file(self.path)

        self.assertTrue(any(issue.rule == "double-subscript" for issue in fix_issues))
        self.assertIn(r"\mathsf{P}_{\mathrm{dox},M}", fixed)
        self.assertIn(r"\mathsf{P}_{\mathrm{ex\text{-}ante},M}", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_parenthesized_superscripts_get_braced(self) -> None:
        self.path.write_text(
            "$$\n"
            r"\forall k_1, k_2 \in \mathbb{N}, \quad k_1 < k_2 \le N "
            r"\implies S^_(k_1) \subsetneq S^_(k_2)"
            "\n$$\n\n"
            "$$\n"
            r"\forall S \subseteq E_1(m), \quad |S| \le k \wedge "
            r"S \neq S^_(k) \implies S^_(k) \succ_{\text{Menger}} S"
            "\n$$\n\n"
            "$$\n"
            r"S^*(k_1) \subsetneq S^*(k_2) \wedge S^*(k) \neq S"
            "\n$$\n",
            encoding="utf-8",
        )

        issues = check_file(self.path)
        self.assertEqual(
            sum(issue.rule == "missing-open-brace-superscript" for issue in issues),
            4,
        )

        fix_issues, fixed = self.fixer.audit_file(self.path)

        self.assertTrue(
            any(issue.rule == "missing-open-brace-superscript" for issue in fix_issues)
        )
        self.assertIn(r"S^{(k_1)}", fixed)
        self.assertIn(r"S^{(k_2)}", fixed)
        self.assertEqual(fixed.count(r"S^{(k)}"), 2)
        self.assertIn(r"S^{\ast}(k_1)", fixed)
        self.assertIn(r"S^{\ast}(k_2)", fixed)
        self.assertIn(r"S^{\ast}(k)", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_corrupt_text_command_and_overescaped_proof_symbol_are_repaired(self) -> None:
        bad_text = r"\mathrm{ex" + "\text{-}ante}"
        self.path.write_text("$$\n" + bad_text + r"\quad \\square" + "\n$$\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("corrupted-text-command", {issue.rule for issue in issues})
        self.assertIn("overescaped-proof-symbol", {issue.rule for issue in issues})

        _fix_issues, fixed = self.fixer.audit_file(self.path)

        self.assertIn(r"\mathrm{ex\text{-}ante}", fixed)
        self.assertIn(r"\square", fixed)
        self.assertNotIn(r"\\square", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_single_backslash_at_aligned_row_end_is_found_and_fixed(self) -> None:
        malformed = "$$\n" + r"\begin{aligned}" + "\n" + r"a&=b" + "\\" + "\n&c" + "\n" + r"\end{aligned}" + "\n$$\n"
        self.path.write_text(malformed, encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("malformed-aligned-row-separator", {issue.rule for issue in issues})

        _fix_issues, fixed = self.fixer.audit_file(self.path)

        self.assertIn(r"a&=b\\" + "\n&c", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_valid_aligned_rows_are_preserved(self) -> None:
        source = (
            "$$\n"
            r"\begin{aligned}"
            "\n"
            r"a&=b\\"
            "\n"
            r"&=c"
            "\n"
            r"\end{aligned}"
            "\n$$\n"
        )
        self.path.write_text(source, encoding="utf-8")

        issues, fixed = self.fixer.audit_file(self.path)

        self.assertEqual(issues, [])
        self.assertEqual(fixed, source)

    def test_prose_math_command_and_missing_apostrophe_are_repaired(self) -> None:
        self.path.write_text(r"The agent s ranking has \succ in the proof." + "\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("math-command-outside-math", {issue.rule for issue in issues})
        self.assertIn("missing-apostrophe-or-character", {issue.rule for issue in issues})

        _fix_issues, fixed = self.fixer.audit_file(self.path)

        self.assertIn("agent's", fixed)
        self.assertIn(r"$\succ$", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_ampersand_in_text_is_flagged_and_repaired(self) -> None:
        self.path.write_text(r"Costs are ($F_{\text{R\&D}} > 0$)." + "\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("ampersand-in-text", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("ampersand-in-text", {issue.rule for issue in fix_issues})
        self.assertIn(r"$F_{\text{RD}} > 0$", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_unspaced_relational_operator_is_flagged_and_repaired(self) -> None:
        self.path.write_text("$$\n" + r"s<t \wedge w>t \wedge t<u" + "\n$$\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unspaced-relational-operator", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unspaced-relational-operator", {issue.rule for issue in fix_issues})
        self.assertIn(r"s < t \wedge w > t \wedge t < u", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_parenthesized_inline_math_is_flagged_and_repaired(self) -> None:
        self.path.write_text(r"Estimator ($\hat{\sigma}^2 = f(\sigma^2)$)." + "\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("parenthesized-inline-math", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("parenthesized-inline-math", {issue.rule for issue in fix_issues})
        self.assertIn(r"( $\hat{\sigma}^2 = f(\sigma^2)$ )", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_unbraced_star_superscript_in_display_math_is_flagged_and_repaired(self) -> None:
        self.path.write_text("$$\n" + r"\Gamma_0 \sqsubseteq \Gamma^*, \quad \Gamma^*(m^*) = \mathcal{I}" + "\n$$\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unbraced-star-superscript", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unbraced-star-superscript", {issue.rule for issue in fix_issues})
        self.assertIn(r"\Gamma_0 \sqsubseteq \Gamma^{\ast}, \quad \Gamma^{\ast}(m^{\ast}) = \mathcal{I}", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_unprotected_inline_math_with_escaped_braces_is_flagged_and_repaired(self) -> None:
        self.path.write_text(r"The image of $\{0, \dots, k-1\}$ under mapping." + "\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in fix_issues})
        self.assertIn(r"$`\{0, \dots, k-1\}`$", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_unprotected_inline_subscript_with_prime_is_flagged_and_repaired(self) -> None:
        self.path.write_text(r"Yielding $P'_{\text{wage}} \le P_{\text{wage}}$." + "\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in fix_issues})
        self.assertIn(r"$`P'_{\text{wage}} \le P_{\text{wage}}`$", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_unprotected_parenthesized_subscript_is_flagged_and_repaired(self) -> None:
        self.path.write_text(r"Purposefulness ($\mathsf{P}_{\mathrm{ex\text{-}ante},M}$) in that rivals." + "\n", encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in fix_issues})
        self.assertIn(r"( $`\mathsf{P}_{\mathrm{ex\text{-}ante},M}`$ )", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_parenthesized_inline_math_with_surrounding_prose(self) -> None:
        text = (
            r"Productive entrepreneurs face input costs (Chapter 9, Definition 9.17: $C_P(\alpha) = \sum_m P_m u(\alpha, m)$) "
            r"and land parcels with zero reproduction capability ($y(\alpha, m_R) = 0$ for all feasible $\alpha \in \mathcal{A}$)."
            "\n"
        )
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertTrue(any(issue.rule == "parenthesized-inline-math" for issue in issues))

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertTrue(any(issue.rule == "parenthesized-inline-math" for issue in fix_issues))
        self.assertIn(r"(Chapter 9, Definition 9.17: $C_P(\alpha) = \sum_m P_m u(\alpha, m)$ )", fixed)
        self.assertIn(r"( $y(\alpha, m_R) = 0$ for all feasible $\alpha \in \mathcal{A}$)", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_inline_matrix_single_backslash_is_flagged_and_repaired(self) -> None:
        self.path.write_text(
            r"- State vector $\mathbf{x}(t) = \begin{pmatrix} K_P(t) - K_P^{\ast} \ w_P(t) - w_P^{\ast} \end{pmatrix}$:" + "\n",
            encoding="utf-8",
        )

        issues = check_file(self.path)
        rules = {issue.rule for issue in issues}
        self.assertIn("malformed-matrix-row-separator", rules)
        self.assertIn("unprotected-inline-math", rules)

        fix_issues, fixed = self.fixer.audit_file(self.path)
        fix_rules = {issue.rule for issue in fix_issues}
        self.assertIn("malformed-matrix-row-separator", fix_rules)
        self.assertIn("unprotected-inline-math", fix_rules)
        self.assertIn(
            r"$`\mathbf{x}(t) = \begin{pmatrix} K_P(t) - K_P^{\ast} \\ w_P(t) - w_P^{\ast} \end{pmatrix}`$",
            fixed,
        )
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_display_matrix_single_backslash_is_flagged_and_repaired(self) -> None:
        text = (
            "$$\n"
            r"\mathbf{x}(t) = \begin{pmatrix} K_P(t) - K_P^{\ast} \ w_P(t) - w_P^{\ast} \end{pmatrix}"
            "\n$$\n"
        )
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("malformed-matrix-row-separator", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("malformed-matrix-row-separator", {issue.rule for issue in fix_issues})
        self.assertIn(
            r"\mathbf{x}(t) = \begin{pmatrix} K_P(t) - K_P^{\ast} \\ w_P(t) - w_P^{\ast} \end{pmatrix}",
            fixed,
        )
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_inline_matrix_with_double_backslash_is_flagged_and_protected(self) -> None:
        self.path.write_text(
            r"- State vector $\mathbf{x}(t) = \begin{pmatrix} K_P(t) - K_P^{\ast} \\ w_P(t) - w_P^{\ast} \end{pmatrix}$:" + "\n",
            encoding="utf-8",
        )

        issues = check_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in fix_issues})
        self.assertIn(
            r"$`\mathbf{x}(t) = \begin{pmatrix} K_P(t) - K_P^{\ast} \\ w_P(t) - w_P^{\ast} \end{pmatrix}`$",
            fixed,
        )
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_indented_prose_math_is_flagged_and_repaired(self) -> None:
        text = (
            "$$\n"
            r"r_R = \frac{R}{P_R}"
            "\n$$\n\n"
            r"     (in continuous target notation: $\partial r_R / \partial P_R = -R / P_R^2 < 0$)."
            "\n"
        )
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        rules = {issue.rule for issue in issues}
        self.assertIn("indented-prose-math", rules)
        self.assertIn("parenthesized-inline-math", rules)

        fix_issues, fixed = self.fixer.audit_file(self.path)
        fix_rules = {issue.rule for issue in fix_issues}
        self.assertIn("indented-prose-math", fix_rules)
        self.assertIn("parenthesized-inline-math", fix_rules)
        self.assertIn(
            r"   (in continuous target notation: $\partial r_R / \partial P_R = -R / P_R^2 < 0$ ).",
            fixed,
        )
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_nested_list_item_with_math_is_not_flagged_as_indented_prose(self) -> None:
        text = "    - Since $b \\in S'$, $S'$ is non-empty.\n"
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertNotIn("indented-prose-math", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertNotIn("indented-prose-math", {issue.rule for issue in fix_issues})
        self.assertEqual(fixed, text)

    def test_inline_math_with_escaped_dollar_is_flagged_and_protected(self) -> None:
        text = (
            r"Equating $\Delta W_{\text{gain}} + \Delta W_{\text{loss}} = \$10,000 - \$5,000 = +\$5,000 > 0$ with an increase"
            "\n"
        )
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unprotected-inline-math", {issue.rule for issue in fix_issues})
        self.assertIn(
            r"$`\Delta W_{\text{gain}} + \Delta W_{\text{loss}} = \$10,000 - \$5,000 = +\$5,000 > 0`$",
            fixed,
        )
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_inline_math_with_bare_currency_dollar_is_flagged_and_repaired(self) -> None:
        text = (
            r"Equating $\Delta W_{\text{gain}} + \Delta W_{\text{loss}} = $10,000 - $5,000 = +$5,000 > 0$ with an increase"
            "\n"
        )
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertTrue(len(issues) > 0)

        fix_issues, fixed = self.fixer.audit_file(self.path)
        fix_rules = {issue.rule for issue in fix_issues}
        self.assertIn("unescaped-currency-symbol", fix_rules)
        self.assertIn("unprotected-inline-math", fix_rules)
        self.assertIn(
            r"$`\Delta W_{\text{gain}} + \Delta W_{\text{loss}} = \$10,000 - \$5,000 = +\$5,000 > 0`$",
            fixed,
        )
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_unescaped_delimiter_brace_in_display_math_is_flagged_and_repaired(self) -> None:
        text = (
            "$$\n"
            + r"\mathcal{S}(\omega, m, B, x, \text{Cohort}) = \left{ i \in \text{Cohort} \mid \sum_{k} P^{\sup}_k x_{i,k} \le \omega_i(m) \right}."
            + "\n$$\n"
        )
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unescaped-delimiter-brace", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unescaped-delimiter-brace", {issue.rule for issue in fix_issues})
        self.assertIn(r"\left\lbrace", fixed)
        self.assertIn(r"\right\rbrace.", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_unescaped_delimiter_brace_in_inline_math_is_flagged_and_repaired(self) -> None:
        text = r"The cohort is $\left{ x \mid x > 0 \right}$." + "\n"
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unescaped-delimiter-brace", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        fix_rules = {issue.rule for issue in fix_issues}
        self.assertIn("unescaped-delimiter-brace", fix_rules)
        self.assertIn(r"\left\lbrace", fixed)
        self.assertIn(r"\right\rbrace", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_unescaped_delimiter_brace_with_spaces_and_middle(self) -> None:
        text = "$$\n" + r"\left { x \in X \middle } y \in Y \right }" + "\n$$\n"
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("unescaped-delimiter-brace", {issue.rule for issue in issues})

        fix_issues, fixed = self.fixer.audit_file(self.path)
        self.assertIn("unescaped-delimiter-brace", {issue.rule for issue in fix_issues})
        self.assertIn(r"\left\lbrace", fixed)
        self.assertIn(r"\middle\rbrace", fixed)
        self.assertIn(r"\right\rbrace", fixed)
        self.path.write_text(fixed, encoding="utf-8")
        self.assertEqual(check_file(self.path), [])

    def test_currency_math_collision_is_flagged(self) -> None:
        text = r"The total was \$12,470.0B ($\Delta_{\mathrm{overhang}}$)." + "\n"
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("currency-math-collision", {issue.rule for issue in issues})

    def test_currency_table_collision_is_flagged(self) -> None:
        text = "| Column 1 | Column 2 |\n|---|---|\n| \\$12,470.0B | \\$3,390.0B |\n"
        self.path.write_text(text, encoding="utf-8")

        issues = check_file(self.path)
        self.assertIn("currency-table-collision", {issue.rule for issue in issues})


if __name__ == "__main__":
    unittest.main()
