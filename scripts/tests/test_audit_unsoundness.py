#!/usr/bin/env python3
"""
scripts/tests/test_audit_unsoundness.py

Unit test suite for scripts/audit_unsoundness.py.
Tests parsing of output sections, severity categorization, and CLI options.
"""

import unittest
from pathlib import Path
import sys

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from audit_unsoundness import parse_lean_audit_output


SAMPLE_OUTPUT = """================================================================================
PRAXEOLOGY LEAN — FORMAL UNSOUNDNESS & CIRCULARITY AUDIT
================================================================================

Total Findings: 4
  • HIGH severity (A->A, 100% assumed conjuncts, hyp-apply, unused active hyps): 2
  • MEDIUM severity (majority assumed conjuncts, evidence repackaging): 1
  • LOW severity (underscore-prefixed unused hyps):                     1

--- HIGH SEVERITY FINDINGS ---
[HYP_APPLY] Praxeology/BusinessCycle/Information.lean:57
  Declaration: Praxeology.ActionFrame.same_market_signal_indistinguishable
  Details:     Proof term is a direct bound-variable / hypothesis application

[100%_CONJUNCTS_ASSUMED] Praxeology/FirmBoundary.lean:580
  Declaration: Praxeology.viable_coalescence_window
  Details:     All 3/3 conclusion conjuncts are directly present in hypotheses

--- MEDIUM SEVERITY FINDINGS ---
[MAJORITY_CONJUNCTS_ASSUMED] Praxeology/BusinessCycle/MasterResults.lean:249
  Declaration: Praxeology.assemble_five_project_cycle_conclusion
  Details:     9/12 conclusion conjuncts are directly present in hypotheses

--- LOW SEVERITY FINDINGS ---
[UNUSED_HYPOTHESIS] Praxeology/Action.lean:1110
  Declaration: Praxeology.universal_action_not_proved_by_local_assertion
  Details:     Hypothesis(es) unused in proof: [_h_idle]

================================================================================
"""


class TestAuditUnsoundness(unittest.TestCase):
    def test_parse_summary(self):
        parsed = parse_lean_audit_output(SAMPLE_OUTPUT)
        self.assertEqual(parsed["summary"]["total"], 4)
        self.assertEqual(parsed["summary"]["high"], 2)
        self.assertEqual(parsed["summary"]["medium"], 1)
        self.assertEqual(parsed["summary"]["low"], 1)

    def test_parse_high_findings(self):
        parsed = parse_lean_audit_output(SAMPLE_OUTPUT)
        high = parsed["high_findings"]
        self.assertEqual(len(high), 2)
        self.assertEqual(high[0]["category"], "HYP_APPLY")
        self.assertEqual(high[0]["file"], "Praxeology/BusinessCycle/Information.lean")
        self.assertEqual(high[0]["line"], "57")
        self.assertEqual(high[0]["declaration"], "Praxeology.ActionFrame.same_market_signal_indistinguishable")

        self.assertEqual(high[1]["category"], "100%_CONJUNCTS_ASSUMED")
        self.assertEqual(high[1]["file"], "Praxeology/FirmBoundary.lean")
        self.assertEqual(high[1]["line"], "580")
        self.assertEqual(high[1]["declaration"], "Praxeology.viable_coalescence_window")

    def test_parse_medium_findings(self):
        parsed = parse_lean_audit_output(SAMPLE_OUTPUT)
        med = parsed["medium_findings"]
        self.assertEqual(len(med), 1)
        self.assertEqual(med[0]["category"], "MAJORITY_CONJUNCTS_ASSUMED")
        self.assertEqual(med[0]["declaration"], "Praxeology.assemble_five_project_cycle_conclusion")

    def test_parse_low_findings(self):
        parsed = parse_lean_audit_output(SAMPLE_OUTPUT)
        low = parsed["low_findings"]
        self.assertEqual(len(low), 1)
        self.assertEqual(low[0]["category"], "UNUSED_HYPOTHESIS")
        self.assertEqual(low[0]["file"], "Praxeology/Action.lean")


if __name__ == "__main__":
    unittest.main()
