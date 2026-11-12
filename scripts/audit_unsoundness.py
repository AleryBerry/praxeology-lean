#!/usr/bin/env python3
"""
scripts/audit_unsoundness.py

Audits the Praxeology Lean 4 codebase for formal unsoundness, circularities,
propositions assuming the conclusion, A -> A proofs, and trivialities.

Runs the native Lean metaprogram `scripts/audit_unsoundness.lean` via `lake env lean --run`,
providing complete semantic accuracy over elaborated Lean 4 proof terms and types.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_AUDIT_SCRIPT = REPO_ROOT / "scripts" / "audit_unsoundness.lean"


def run_lean_audit() -> str:
    """Executes scripts/audit_unsoundness.lean and captures stdout."""
    if not LEAN_AUDIT_SCRIPT.exists():
        raise FileNotFoundError(f"Lean audit script not found at {LEAN_AUDIT_SCRIPT}")

    cmd = ["lake", "env", "lean", "--run", str(LEAN_AUDIT_SCRIPT)]
    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.write(f"Lean audit failed with returncode {proc.returncode}:\n")
        sys.stderr.write(proc.stderr)
        sys.stderr.write(proc.stdout)
        raise RuntimeError(f"Audit failed with exit code {proc.returncode}")

    return proc.stdout


def parse_lean_audit_output(output: str) -> Dict[str, Any]:
    """Parses the text output of scripts/audit_unsoundness.lean into structured data."""
    summary: Dict[str, int] = {
        "total": 0,
        "high": 0,
        "medium": 0,
        "low": 0,
    }
    high_findings: List[Dict[str, str]] = []
    med_findings: List[Dict[str, str]] = []
    low_findings: List[Dict[str, str]] = []

    m_total = re.search(r"Total Findings:\s+(\d+)", output)
    if m_total:
        summary["total"] = int(m_total.group(1))

    m_high = re.search(r"HIGH severity[^:]*:\s+(\d+)", output)
    if m_high:
        summary["high"] = int(m_high.group(1))

    m_med = re.search(r"MEDIUM severity[^:]*:\s+(\d+)", output)
    if m_med:
        summary["medium"] = int(m_med.group(1))

    m_low = re.search(r"LOW severity[^:]*:\s+(\d+)", output)
    if m_low:
        summary["low"] = int(m_low.group(1))

    def parse_section(header: str, next_header: str | None = None) -> List[Dict[str, str]]:
        if header not in output:
            return []
        start = output.index(header) + len(header)
        end = output.index(next_header, start) if next_header and next_header in output else len(output)
        section_text = output[start:end]

        findings = []
        pattern = re.compile(
            r"\[([^\]]+)\]\s+([^:\s]+):(\d+)\s*\n\s*Declaration:\s*([^\n]+)\s*\n\s*Details:\s*([^\n]+)"
        )
        for m in pattern.finditer(section_text):
            findings.append({
                "category": m.group(1),
                "file": m.group(2),
                "line": m.group(3),
                "declaration": m.group(4).strip(),
                "details": m.group(5).strip(),
            })
        return findings

    high_findings = parse_section("--- HIGH SEVERITY FINDINGS ---", "--- MEDIUM SEVERITY FINDINGS ---")
    med_findings = parse_section("--- MEDIUM SEVERITY FINDINGS ---", "--- LOW SEVERITY FINDINGS ---")
    low_findings = parse_section("--- LOW SEVERITY FINDINGS ---", "================================================================================")

    return {
        "summary": summary,
        "high_findings": high_findings,
        "medium_findings": med_findings,
        "low_findings": low_findings,
        "raw_output": output,
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit Praxeology Lean codebase for formal unsoundness, circularities, and trivialities."
    )
    parser.add_argument("--check", action="store_true", help="Fail with exit code 1 if any HIGH severity findings are detected.")
    parser.add_argument("--json", action="store_true", help="Output results in JSON format.")
    parser.add_argument("--summary", action="store_true", help="Print summary counts only.")
    args = parser.parse_args()

    raw_output = run_lean_audit()
    data = parse_lean_audit_output(raw_output)

    if args.json:
        print(json.dumps(data, indent=2))
    elif args.summary:
        print(f"Total Findings: {data['summary']['total']}")
        print(f"  HIGH severity:   {data['summary']['high']}")
        print(f"  MEDIUM severity: {data['summary']['medium']}")
        print(f"  LOW severity:    {data['summary']['low']}")
    else:
        print(raw_output.strip())

    if args.check and data["summary"]["high"] > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
