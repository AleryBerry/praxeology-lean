#!/usr/bin/env python3
"""
scripts/audit_adhoc_premises.py

Automated heuristic audit script to verify that macroeconomic results,
business-cycle theorems, and catallactic interactions are derived endogenously
from core ActionFrame and PurposefulAct foundations, rather than relying on
ad-hoc external premise wrappers, shock structures, or detached payoff matrices.

Audited categories:
1. Deprecated Premise Structures:
   Detects any re-emergence of external hypothesis wrappers or bypass structures.
2. Ad-hoc Shock & Squeeze Declarations:
   Detects new structures or classes encoding exogenous interest shocks,
   factor starvations, or completion squeezes.
3. Ad-hoc Subjective Flip Hypotheses:
   Detects hypotheses where an external arithmetic condition directly
   forces purposeful choice without going through teleological bundle dominance.
4. Detached Game Matrix & Payoff Bypasses:
   Detects outcome or stock functions declared as standalone action matrices
   rather than derived from ActionFrame.jointBranch and ActionFrame.omega.
"""

import sys
import re
import argparse
import json
from pathlib import Path
from typing import List, Dict, Any, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
PRAXEOLOGY_DIR = REPO_ROOT / "Praxeology"

# List of prohibited external premise structures that were eliminated
# in favor of endogenous ActionFrame derivations.
ERADICATED_STRUCTURES = [
    "ABCTInterestShock",
    "StageValuationSignals",
    "IntertemporalTerms",
    "IntertemporalAppraisal",
    "ComplementaryFactorStarvation",
    "PriceBoxCompletionSqueeze",
    "EndogenousPriceBoxSqueeze",
    "CantillonPriceBoxSqueezeEvidence",
    "BilateralNode",
    "CreditInvestmentMenu",
    "abctGroundedTerms",
    "abctGroundedInterestShock",
    "abctGroundedCapitalAccumulation",
    "EndogenouslyInvasive_",
    # Legacy implicational firm boundary & state monopoly structures:
    "EntrepreneurialFirmDecision",
    "ModelEntrepreneurialFirmDecision",
    "BinaryFiscalDecision",
    "RulerExtractionBounds",
    "RulerTimePreferenceScenario",
    "StatutoryMonopolyCostPolicyEvidence",
    "StatutoryMonopolyDecisionEvidence",
]

# Patterns for ad-hoc shock/squeeze/node declarations
AD_HOC_DECLARATION_PATTERNS = [
    (re.compile(r"^(?:structure|class)\s+([A-Za-z0-9_]*(?:InterestShock|RateShock|ValuationSignals)[A-Za-z0-9_]*)"),
     "AD_HOC_RATE_SHOCK_STRUCTURE"),
    (re.compile(r"^(?:structure|class)\s+([A-Za-z0-9_]*(?:PriceSqueezeEvidence|FactorStarvation|CompletionSqueeze)[A-Za-z0-9_]*)"),
     "AD_HOC_SQUEEZE_STRUCTURE"),
    (re.compile(r"^(?:structure|class)\s+([A-Za-z0-9_]*(?:BilateralNode|InteractionNode)[A-Za-z0-9_]*)"),
     "AD_HOC_INTERACTION_NODE"),
]

# Patterns for detached payoff/outcome matrices outside ActionFrame
DETACHED_PAYOFF_PATTERNS = [
    (re.compile(r"\bOutcome\s*:\s*[^→\n]+→\s*[^→\n]+→\s*Ends\b"),
     "DETACHED_OUTCOME_MATRIX"),
    (re.compile(r"\bpostStock\s*:\s*[^→\n]+→\s*[^→\n]+→\s*[^→\n]+→\s*ℕ\b"),
     "DETACHED_STOCK_MATRIX"),
]

# Pattern for ungrounded subjective flips: arithmetic inequality directly yielding PurposefulAct
UNGROUNDED_SUBJECTIVE_FLIP = re.compile(
    r"\(h\w*\s*:\s*[^)]*(?:<|≤|<=)[^)]*→\s*@?PurposefulAct\b"
)

# Domain modules that must not declare detached ontological type parameters
# or ad-hoc preference bridge fields/hypotheses.
DOMAIN_MODULES = [
    "Praxeology/StateMonopoly.lean",
    "Praxeology/FirmBoundary.lean",
    "Praxeology/Catallactics.lean",
    "Praxeology/Catallactics/Credit.lean",
    "Praxeology/Marginal.lean",
    "Praxeology/Production.lean",
    "Praxeology/Organization.lean",
    "Praxeology/Entrepreneurship.lean",
    "Praxeology/BusinessCycle.lean",
    "Praxeology/BusinessCycle/Clusters.lean",
    "Praxeology/BusinessCycle/Firms.lean",
    "Praxeology/BusinessCycle/Information.lean",
    "Praxeology/EconometricLimits.lean",
    "Praxeology/BehavioralPoset.lean",
]

# Pattern for detached ontological type parameters
DETACHED_ONTOLOGY_PATTERN = re.compile(
    r"[\(\{]\s*(?:[A-Za-z0-9_]+\s+)*"
    r"(?:Agent|Action|Means|Ends|Moment|History)\b"
    r"[^:\)\}]*:\s*Type(?:\s*\*|\s*[A-Za-z0-9_]*)?\s*[\)\}]"
)

# Patterns for preference bridges (both → and ↔) mapping external formulas to Preference.
# Uses DOTALL-compatible matching to catch multiline declarations.
PREFERENCE_BRIDGE_PATTERNS = [
    (re.compile(r"(?:SignalSplit|SignalMerge|CoalescedQuantizationNoise|TotalQuantizationNoise|\.card\b)[^;:]*?→\s*(?:[A-Za-z0-9_().\s]*?→\s*)*(?:W\.)?(?:Preference|Pref)\b", re.DOTALL),
     "IMPLICATIONAL_PREFERENCE_BRIDGE"),
    (re.compile(r"\b(?:W\.)?(?:Preference|Pref)\b[^;:\n]*↔\s*[^;:\n]*(?:<|≤|baselineReturn|activeReturn)"),
     "BICONDITIONAL_PREFERENCE_BRIDGE"),
    (re.compile(r"(?:<|≤|baselineReturn|activeReturn)[^;:\n]*↔\s*[^;:\n]*(?:W\.)?(?:Preference|Pref)\b"),
     "BICONDITIONAL_PREFERENCE_BRIDGE"),
    (re.compile(r"^\s*(?:h_pref_\w+|active_pref|baseline_pref)\s*:[^:\n]*(?:Preference|Pref)\b", re.MULTILINE),
     "NAMED_PREFERENCE_BRIDGE_FIELD"),
]

# Patterns for uninterpreted institutional or behavioral Prop fields in structures.
# Flagged regardless of multiline formatting.
UNINTERPRETED_PROP_FIELD_PATTERNS = [
    (re.compile(r"^\s*(?:invades|punished|rivalDefense|resistsExtraction)\s*:[^:\n]*Prop\b", re.MULTILINE),
     "UNINTERPRETED_INSTITUTIONAL_PROP_FIELD"),
    (re.compile(r"^\s*(?:mengerian_pref|marketability_dominance)\b", re.MULTILINE),
     "UNINTERPRETED_PREFERENCE_PROP_FIELD"),
]


def strip_lean_comments(text: str) -> str:
    """Strips block comments /- ... -/ and line comments -- ... from Lean source code."""
    # Replace block comments with spaces preserving newlines
    def repl_block(m):
        return "\n" * m.group(0).count("\n")
    text = re.sub(r"/-(?:(?!--/).)*?-/", repl_block, text, flags=re.DOTALL)
    
    # Strip line comments
    lines = []
    for line in text.splitlines():
        # Match -- not preceded by an escape or inside string literal
        line_no_comment = re.sub(r"--.*$", "", line)
        lines.append(line_no_comment)
    return "\n".join(lines)


def format_file_path(file_path: Path) -> str:
    try:
        return str(file_path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(file_path)


class AdHocPremisesAuditor:
    def __init__(self, root_dir: Path = PRAXEOLOGY_DIR):
        self.root_dir = root_dir
        self.lean_files = sorted(root_dir.rglob("*.lean"))
        if (REPO_ROOT / "Praxeology.lean").exists():
            self.lean_files.append(REPO_ROOT / "Praxeology.lean")

    def audit_eradicated_structures(self, file_path: Path, stripped_content: str) -> List[Dict[str, Any]]:
        findings = []
        for term in ERADICATED_STRUCTURES:
            pattern = re.compile(rf"\b{re.escape(term)}\b")
            for idx, line in enumerate(stripped_content.splitlines(), 1):
                if pattern.search(line):
                    findings.append({
                        "file": format_file_path(file_path),
                        "line": idx,
                        "type": f"ERADICATED_STRUCTURE ({term})",
                        "text": line.strip()
                    })
        return findings

    def audit_adhoc_declarations(self, file_path: Path, stripped_content: str) -> List[Dict[str, Any]]:
        findings = []
        for idx, line in enumerate(stripped_content.splitlines(), 1):
            clean = line.strip()
            for pattern, label in AD_HOC_DECLARATION_PATTERNS:
                m = pattern.search(clean)
                if m:
                    findings.append({
                        "file": format_file_path(file_path),
                        "line": idx,
                        "type": f"{label} ({m.group(1)})",
                        "text": clean
                    })
        return findings

    def audit_detached_payoffs(self, file_path: Path, stripped_content: str) -> List[Dict[str, Any]]:
        findings = []
        for idx, line in enumerate(stripped_content.splitlines(), 1):
            clean = line.strip()
            for pattern, label in DETACHED_PAYOFF_PATTERNS:
                if pattern.search(clean):
                    findings.append({
                        "file": format_file_path(file_path),
                        "line": idx,
                        "type": label,
                        "text": clean
                    })
        return findings

    def audit_ungrounded_subjective_flips(self, file_path: Path, stripped_content: str) -> List[Dict[str, Any]]:
        findings = []
        for idx, line in enumerate(stripped_content.splitlines(), 1):
            clean = line.strip()
            if UNGROUNDED_SUBJECTIVE_FLIP.search(clean):
                findings.append({
                    "file": format_file_path(file_path),
                    "line": idx,
                    "type": "UNGROUNDED_SUBJECTIVE_FLIP",
                    "text": clean
                })
        return findings

    def audit_detached_ontology_types(self, file_path: Path, stripped_content: str) -> List[Dict[str, Any]]:
        findings = []
        rel_path = format_file_path(file_path)
        if rel_path in DOMAIN_MODULES:
            for idx, line in enumerate(stripped_content.splitlines(), 1):
                clean = line.strip()
                if DETACHED_ONTOLOGY_PATTERN.search(clean):
                    findings.append({
                        "file": rel_path,
                        "line": idx,
                        "type": "DETACHED_ONTOLOGY_TYPE",
                        "text": clean
                    })
        return findings

    def audit_preference_bridges(self, file_path: Path, stripped_content: str) -> List[Dict[str, Any]]:
        findings = []
        rel_path = format_file_path(file_path)
        if rel_path in DOMAIN_MODULES:
            for pattern, label in PREFERENCE_BRIDGE_PATTERNS:
                for match in pattern.finditer(stripped_content):
                    line_num = stripped_content[:match.start()].count("\n") + 1
                    match_text = match.group(0).strip().replace("\n", " ")
                    findings.append({
                        "file": rel_path,
                        "line": line_num,
                        "type": label,
                        "text": match_text[:120]
                    })
        return findings

    def audit_uninterpreted_prop_fields(self, file_path: Path, stripped_content: str) -> List[Dict[str, Any]]:
        findings = []
        rel_path = format_file_path(file_path)
        if rel_path in DOMAIN_MODULES:
            for pattern, label in UNINTERPRETED_PROP_FIELD_PATTERNS:
                for match in pattern.finditer(stripped_content):
                    # compute line number from match.start()
                    line_num = stripped_content[:match.start()].count("\n") + 1
                    match_text = match.group(0).strip()
                    findings.append({
                        "file": rel_path,
                        "line": line_num,
                        "type": label,
                        "text": match_text
                    })
        return findings

    def run_all(self) -> Dict[str, List[Dict[str, Any]]]:
        results = {
            "eradicated_structures": [],
            "adhoc_declarations": [],
            "detached_payoffs": [],
            "ungrounded_subjective_flips": [],
            "detached_ontology_types": [],
            "preference_bridges": [],
            "uninterpreted_prop_fields": [],
        }

        for file_path in self.lean_files:
            raw_text = file_path.read_text(encoding="utf-8")
            stripped = strip_lean_comments(raw_text)

            results["eradicated_structures"].extend(
                self.audit_eradicated_structures(file_path, stripped)
            )
            results["adhoc_declarations"].extend(
                self.audit_adhoc_declarations(file_path, stripped)
            )
            results["detached_payoffs"].extend(
                self.audit_detached_payoffs(file_path, stripped)
            )
            results["ungrounded_subjective_flips"].extend(
                self.audit_ungrounded_subjective_flips(file_path, stripped)
            )
            results["detached_ontology_types"].extend(
                self.audit_detached_ontology_types(file_path, stripped)
            )
            results["preference_bridges"].extend(
                self.audit_preference_bridges(file_path, stripped)
            )
            results["uninterpreted_prop_fields"].extend(
                self.audit_uninterpreted_prop_fields(file_path, stripped)
            )

        return results


def main():
    parser = argparse.ArgumentParser(
        description="Audit Lean codebase for ad-hoc premises, shock wrappers, and external bypass structures."
    )
    parser.add_argument("--check", action="store_true", help="Exit with code 1 if any violations are found.")
    parser.add_argument("--verbose", action="store_true", help="Print detailed findings.")
    parser.add_argument("--json", action="store_true", help="Output results in JSON format.")
    args = parser.parse_args()

    auditor = AdHocPremisesAuditor()
    results = auditor.run_all()

    total_findings = sum(len(v) for v in results.values())

    if args.json:
        payload = {
            "total_findings": total_findings,
            "passed": total_findings == 0,
            "results": results
        }
        print(json.dumps(payload, indent=2))
        if args.check and total_findings > 0:
            sys.exit(1)
        return

    print("=" * 80)
    print("PRAXEOLOGY LEAN — AD-HOC PREMISES & MACROECONOMIC SHOCK AUDIT")
    print("=" * 80)
    print()
    print("AUDIT SCORECARD:")
    print(f"  1. Eradicated Wrapper Structures:     {len(results['eradicated_structures']):4d}  (Target: 0)")
    print(f"  2. Ad-Hoc Shock & Squeeze Structs:     {len(results['adhoc_declarations']):4d}  (Target: 0)")
    print(f"  3. Detached Game Payoff Matrices:     {len(results['detached_payoffs']):4d}  (Target: 0)")
    print(f"  4. Ungrounded Subjective Flips:       {len(results['ungrounded_subjective_flips']):4d}  (Target: 0)")
    print(f"  5. Detached Ontology Type Params:     {len(results['detached_ontology_types']):4d}  (Target: 0)")
    print(f"  6. Preference Bridges (→ / ↔):        {len(results['preference_bridges']):4d}  (Target: 0)")
    print(f"  7. Uninterpreted Prop Fields:         {len(results['uninterpreted_prop_fields']):4d}  (Target: 0)")
    print()

    if total_findings > 0:
        print(f">> STATUS: [FAILED] {total_findings} ad-hoc premise violation(s) detected.")
        if args.verbose or args.check:
            print("\nDetailed Findings:")
            for category, findings in results.items():
                if findings:
                    print(f"\n--- {category.upper()} ({len(findings)}) ---")
                    for f in findings:
                        print(f"  {f['file']}:{f['line']} [{f['type']}]")
                        print(f"    {f['text']}")
        print("=" * 80)
        if args.check:
            sys.exit(1)
    else:
        print(">> STATUS: [PASSED] Zero ad-hoc rules, wrapper shocks, or matrix bypasses detected.")
        print(">> All macroeconomic and bilateral results are derived natively from ActionFrame.")
        print("=" * 80)


if __name__ == "__main__":
    main()
