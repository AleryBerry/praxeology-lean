#!/usr/bin/env python3
"""
scripts/audit_axiomatic_floor.py

Heuristic source-pattern report for manual review of selected modeling choices.
Findings require semantic review; absence of findings does not establish
theorem validity, axiom independence, or a well-founded economic model.

Five heuristic checks:
1. Omit & Shadow-Structure Detector:
   Detects `omit ... in` and shadow structures (e.g. DoxasticActionFrame).
2. Shadow Primitive Collision Detector:
   Detects external epistemic sets (K, K2, signal) and shadow valuation functors.
3. Implicational Bridge Stuffing Detector:
   Detects hypotheses where arithmetic inequality implies subjective preference directly.
4. Singleton-Collapse Witness Auditor:
   Audits whether MinPlausible collapses to singletons across branched nodes.
"""

import sys
import re
from pathlib import Path
from typing import List, Dict, Any, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
PRAXEOLOGY_DIR = REPO_ROOT / "Praxeology"

class AxiomaticFloorAuditor:
    def __init__(self, root_dir: Path = PRAXEOLOGY_DIR):
        self.root_dir = root_dir
        self.lean_files = sorted(root_dir.rglob("*.lean"))
        if (REPO_ROOT / "Praxeology.lean").exists():
            self.lean_files.append(REPO_ROOT / "Praxeology.lean")

    def audit_omit_and_shadow_structures(self) -> List[Dict[str, Any]]:
        findings = []
        for file in self.lean_files:
            lines = file.read_text(encoding="utf-8").splitlines()
            for idx, line in enumerate(lines, 1):
                clean = line.strip()
                # Skip comments
                if clean.startswith("--") or clean.startswith("/-"):
                    continue
                # Detect omit statements
                if re.search(r"\bomit\b.*?\bin\b", clean):
                    findings.append({
                        "file": str(file.relative_to(REPO_ROOT)),
                        "line": idx,
                        "type": "OMIT_ESCAPE",
                        "text": clean
                    })
                # Detect DoxasticActionFrame definition or usage
                if re.search(r"\bDoxasticActionFrame\b", clean) and not clean.startswith("--"):
                    findings.append({
                        "file": str(file.relative_to(REPO_ROOT)),
                        "line": idx,
                        "type": "SHADOW_STRUCTURE (DoxasticActionFrame)",
                        "text": clean
                    })
        return findings

    def audit_shadow_primitives(self) -> List[Dict[str, Any]]:
        findings = []
        # Patterns for external parameters that bypass core primitives
        patterns = [
            (r"\((?:K|K2|K_2)\s*:\s*Set\s+[^)]+\)", "EXTERNAL_EPISTEMIC_SET (K/K2)"),
            (r"\((?:Valuate)\s*:\s*\([^)]+→\s*ℕ\)\s*→\s*Ends\)", "SHADOW_VALUATION_FUNCTOR"),
            (r"\((?:M)\s*:\s*OrdinalParPricingModel\)", "SHADOW_PRICING_MODEL"),
        ]

        for file in self.lean_files:
            content = file.read_text(encoding="utf-8")
            lines = content.splitlines()
            for idx, line in enumerate(lines, 1):
                clean = line.strip()
                if clean.startswith("--") or clean.startswith("/-"):
                    continue
                for pat, label in patterns:
                    if re.search(pat, clean):
                        findings.append({
                            "file": str(file.relative_to(REPO_ROOT)),
                            "line": idx,
                            "type": label,
                            "text": clean
                        })
        return findings

    def audit_implicational_bridges(self) -> List[Dict[str, Any]]:
        findings = []
        # Hypotheses of form: h_... : [arithmetic expr with < or ≤] → [something with Pref]
        bridge_pat = re.compile(
            r"\(h_\w+\s*:\s*[^)]*(?:<|≤)[^)]*→\s*[^)]*(?:Preference|Pref)[^)]*\)"
        )

        for file in self.lean_files:
            lines = file.read_text(encoding="utf-8").splitlines()
            for idx, line in enumerate(lines, 1):
                clean = line.strip()
                if clean.startswith("--") or clean.startswith("/-"):
                    continue
                match = bridge_pat.search(clean)
                if match:
                    findings.append({
                        "file": str(file.relative_to(REPO_ROOT)),
                        "line": idx,
                        "type": "IMPLICATIONAL_BRIDGE_STUFFING",
                        "text": clean
                    })
        return findings

    def audit_singleton_collapses(self) -> List[Dict[str, Any]]:
        findings = []
        # Look for theorems explicitly proving MinPlausible collapses to singleton {c}
        singleton_proof_pat = re.compile(
            r"theorem\s+(\w+)\s*:[^=]+MinPlausible\s+[^=]+=\s*\{[^,}]+\}"
        )
        # Or theorems specifically proving abct_min_plausible_eq
        for file in self.lean_files:
            content = file.read_text(encoding="utf-8")
            lines = content.splitlines()
            for idx, line in enumerate(lines, 1):
                clean = line.strip()
                if "abct_min_plausible_eq" in clean and (
                    "theorem" in clean or "lemma" in clean or "def" in clean
                ):
                    findings.append({
                        "file": str(file.relative_to(REPO_ROOT)),
                        "line": idx,
                        "type": "FORCED_SINGLETON_COLLAPSE (abct_min_plausible_eq)",
                        "text": clean
                    })
                elif (
                    "MinimalPlausibleStratum" in clean and "= {" in clean
                    and not clean.startswith("--")
                ):
                    # Check if it's proving a singleton
                    if re.search(r"=\s*\{[0-9a-zA-Z_.]+\}", clean):
                        findings.append({
                            "file": str(file.relative_to(REPO_ROOT)),
                            "line": idx,
                            "type": "SINGLETON_STRATUM_COLLAPSE",
                            "text": clean
                        })
        return findings

    def run_full_audit(self) -> Dict[str, Any]:
        omit_findings = self.audit_omit_and_shadow_structures()
        shadow_findings = self.audit_shadow_primitives()
        bridge_findings = self.audit_implicational_bridges()
        singleton_findings = self.audit_singleton_collapses()

        # Categorize omits vs shadow structures
        omits = [f for f in omit_findings if f["type"] == "OMIT_ESCAPE"]
        shadow_structs = [f for f in omit_findings if "SHADOW_STRUCTURE" in f["type"]]

        scorecard = {
            "omit_count": len(omits),
            "shadow_structure_count": len(shadow_structs),
            "shadow_primitive_count": len(shadow_findings),
            "implicational_bridge_count": len(bridge_findings),
            "singleton_collapse_count": len(singleton_findings),
        }

        return {
            "scorecard": scorecard,
            "omits": omits,
            "shadow_structs": shadow_structs,
            "shadow_primitives": shadow_findings,
            "bridges": bridge_findings,
            "singleton_collapses": singleton_findings
        }


def print_report(data: Dict[str, Any]):
    sc = data["scorecard"]
    print("=" * 80)
    print("PRAXEOLOGY LEAN — ADVISORY MODELING-PATTERN REPORT")
    print("=" * 80)
    print()
    print("Pattern counts (review each hit in context):")
    print(f"  1. `omit` annotations:              {sc['omit_count']:>4}")
    print(f"  2. Shadow-structure names:          {sc['shadow_structure_count']:>4}")
    print(f"  3. Shadow-primitive patterns:       {sc['shadow_primitive_count']:>4}")
    print(f"  4. Arithmetic-bridge patterns:      {sc['implicational_bridge_count']:>4}")
    print(f"  5. Singleton-plausibility patterns: {sc['singleton_collapse_count']:>4}")
    print()

    has_findings = any(sc.values())
    if has_findings:
        print(">> Pattern hits follow; inspect each declaration's Lean type and proof.")
        print()
        print("-" * 80)
        print("DETAILED PATTERN FINDINGS:")
        print("-" * 80)

        if data["omits"]:
            print(f"\n[!] `omit` Escapes ({len(data['omits'])} occurrences):")
            for item in data["omits"][:15]:
                print(f"    - {item['file']}:{item['line']} -> {item['text']}")
            if len(data["omits"]) > 15:
                print(f"    ... and {len(data['omits']) - 15} more.")

        if data["shadow_structs"]:
            print(f"\n[!] Shadow Structures ({len(data['shadow_structs'])} occurrences):")
            for item in data["shadow_structs"][:10]:
                print(f"    - {item['file']}:{item['line']} -> {item['text']}")
            if len(data["shadow_structs"]) > 10:
                print(f"    ... and {len(data['shadow_structs']) - 10} more.")

        if data["shadow_primitives"]:
            print(f"\n[!] Shadow Primitives ({len(data['shadow_primitives'])} occurrences):")
            for item in data["shadow_primitives"]:
                print(f"    - {item['file']}:{item['line']} [{item['type']}] -> {item['text']}")

        if data["bridges"]:
            print(f"\n[!] Implicational Bridges ({len(data['bridges'])} occurrences):")
            for item in data["bridges"]:
                print(f"    - {item['file']}:{item['line']} -> {item['text']}")

        if data["singleton_collapses"]:
            count = len(data['singleton_collapses'])
            print(f"\n[!] Singleton Plausibility Collapses ({count} occurrences):")
            for item in data["singleton_collapses"]:
                print(f"    - {item['file']}:{item['line']} -> {item['text']}")
    else:
        print(">> No configured patterns found; this is not a semantic verification result.")

    print("This report is advisory and never assigns semantic pass/fail status.")

    print()
    print("=" * 80)


def main():
    auditor = AxiomaticFloorAuditor()
    data = auditor.run_full_audit()
    print_report(data)
    sys.exit(0)


if __name__ == "__main__":
    main()
