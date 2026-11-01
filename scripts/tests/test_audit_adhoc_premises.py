#!/usr/bin/env python3
"""
scripts/tests/test_audit_adhoc_premises.py

Unit test suite for scripts/audit_adhoc_premises.py.
Tests detection of eradicated wrapper structures, ad-hoc shock structures,
detached game matrices, ungrounded subjective flips, and verifies clean pass on codebase.
"""

import unittest
from pathlib import Path
import sys

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from audit_adhoc_premises import (
    AdHocPremisesAuditor,
    strip_lean_comments,
    ERADICATED_STRUCTURES,
)

REPO_ROOT = SCRIPTS_DIR.parent


class TestAuditAdHocPremises(unittest.TestCase):
    def setUp(self):
        self.auditor = AdHocPremisesAuditor()

    def test_current_codebase_passes(self):
        """The actual Praxeology codebase must contain zero ad-hoc premise violations."""
        results = self.auditor.run_all()
        for category, findings in results.items():
            self.assertEqual(
                len(findings),
                0,
                f"Expected 0 findings in category '{category}', got {len(findings)}:\n{findings}"
            )

    def test_detects_eradicated_structures(self):
        """Verifies that all eradicated wrapper structures are detected if reintroduced."""
        for struct_name in ERADICATED_STRUCTURES:
            synthetic_snippet = f"structure {struct_name} (W : ActionFrame) where\n  val : ℕ"
            stripped = strip_lean_comments(synthetic_snippet)
            findings = self.auditor.audit_eradicated_structures(Path("synthetic.lean"), stripped)
            self.assertTrue(
                any(struct_name in f["type"] for f in findings),
                f"Failed to detect eradicated structure '{struct_name}'"
            )

    def test_detects_adhoc_shock_and_squeeze_declarations(self):
        """Verifies that ad-hoc shock, squeeze, and interaction node structures are flagged."""
        synthetic_cases = [
            ("structure CustomRateShock (W : ActionFrame) where\n  rate : ℕ", "AD_HOC_RATE_SHOCK_STRUCTURE"),
            ("structure MacroInterestShock (W : ActionFrame) where\n  spread : ℕ", "AD_HOC_RATE_SHOCK_STRUCTURE"),
            ("structure FactorStarvationEvidence (W : ActionFrame) where\n  factor : ℕ", "AD_HOC_SQUEEZE_STRUCTURE"),
            ("structure ExternalCompletionSqueeze (W : ActionFrame) where\n  shortfall : ℕ", "AD_HOC_SQUEEZE_STRUCTURE"),
            ("structure DetachedInteractionNode (W : ActionFrame) where\n  node : ℕ", "AD_HOC_INTERACTION_NODE"),
            ("class InteractionNodeInstance (W : ActionFrame) where\n  node : ℕ", "AD_HOC_INTERACTION_NODE"),
        ]

        for code, expected_type in synthetic_cases:
            stripped = strip_lean_comments(code)
            findings = self.auditor.audit_adhoc_declarations(Path("synthetic.lean"), stripped)
            self.assertTrue(
                any(expected_type in f["type"] for f in findings),
                f"Failed to detect ad-hoc declaration in:\n{code}"
            )

    def test_detects_detached_payoff_matrices(self):
        """Verifies that matrix outcome functions declared outside ActionFrame are detected."""
        synthetic_cases = [
            ("Outcome : Action → Action → Ends", "DETACHED_OUTCOME_MATRIX"),
            ("postStock : Action → Action → Means → ℕ", "DETACHED_STOCK_MATRIX"),
        ]

        for code, expected_type in synthetic_cases:
            stripped = strip_lean_comments(code)
            findings = self.auditor.audit_detached_payoffs(Path("synthetic.lean"), stripped)
            self.assertTrue(
                any(f["type"] == expected_type for f in findings),
                f"Failed to detect detached payoff pattern in:\n{code}"
            )

    def test_detects_ungrounded_subjective_flips(self):
        """Verifies that ungrounded subjective flips bypassing bundle dominance are detected."""
        code = "theorem bad_flip (h_flip : r < r_nat → PurposefulAct a t h α) : True := trivial"
        stripped = strip_lean_comments(code)
        findings = self.auditor.audit_ungrounded_subjective_flips(Path("synthetic.lean"), stripped)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["type"], "UNGROUNDED_SUBJECTIVE_FLIP")

    def test_strip_comments_ignores_commented_code(self):
        """Comments mentioning deprecated names should not produce false positives."""
        commented_snippet = """
        -- An external shock structure was commented out here.
        /-
        structure StandalonePayoffMatrix (W : ActionFrame) where
          Outcome : Action → Action → Ends
        -/
        def valid_definition : Nat := 42
        """
        stripped = strip_lean_comments(commented_snippet)
        findings_eradicated = self.auditor.audit_eradicated_structures(Path("test.lean"), stripped)
        findings_declarations = self.auditor.audit_adhoc_declarations(Path("test.lean"), stripped)
        findings_payoffs = self.auditor.audit_detached_payoffs(Path("test.lean"), stripped)

        self.assertEqual(len(findings_eradicated), 0)
        self.assertEqual(len(findings_declarations), 0)
        self.assertEqual(len(findings_payoffs), 0)


if __name__ == "__main__":
    unittest.main()
