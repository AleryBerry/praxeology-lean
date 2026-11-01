#!/usr/bin/env python3
"""Audit transitive axiom dependencies and report results per Lean source file."""

from __future__ import annotations

import argparse
from collections import Counter
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def build_lean_audit(prefix: str | None = None, exact: str | None = None) -> str:
    if exact:
        filter_expr = f'n.toString == "{exact}"'
    elif prefix:
        filter_expr = (
            f'n.toString.startsWith "{prefix}" || '
            f'n.toString.contains "_private.{prefix}"'
        )
    else:
        filter_expr = (
            'n.toString.startsWith "Praxeology." || '
            'n.toString.contains "_private.Praxeology."'
        )

    return f'''import Praxeology
open Lean Elab Command
run_elab do
  let env ← getEnv
  let names := env.constants.toList.map (·.1) |>.filter fun n =>
    {filter_expr}
  logInfo m!"AUDIT|{{names.length}}"
  for n in names do
    let moduleName :=
      (env.getModuleIdxFor? n).map (fun idx => env.header.moduleNames[idx]!) |>.getD env.mainModule
    let axs ← collectAxioms n
    let axText := String.intercalate "," (axs.toList.map Name.toString)
    logInfo m!"DECL|{{moduleName}}|{{n}}|{{axText}}"
'''


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--strict",
        action="store_true",
        help="return failure if any audited declaration has an axiom dependency",
    )
    parser.add_argument(
        "--prefix",
        type=str,
        default=None,
        help="filter audited declarations by symbol prefix (e.g. Praxeology.FiscalTransferSystem)",
    )
    parser.add_argument(
        "--exact",
        type=str,
        default=None,
        help="audit a single exact declaration (e.g. Praxeology.calhoun_fiscal_class_partition)",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="print all axiom-dependent declarations within each file",
    )
    parser.add_argument(
        "--by-axiom",
        action="store_true",
        help="summarize dependent declarations by transitive axiom within each file",
    )
    parser.add_argument(
        "--by-file",
        action="store_true",
        help="print the deduplicated union of transitive axiom dependencies per file",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=20,
        help="maximum dependency examples to print per file (default: 20)",
    )
    args = parser.parse_args()

    lean_code = build_lean_audit(args.prefix, args.exact)
    proc = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=lean_code,
        text=True,
        cwd=ROOT,
        capture_output=True,
        check=False,
    )
    if proc.returncode:
        sys.stderr.write(proc.stderr)
        sys.stderr.write(proc.stdout)
        return proc.returncode

    records_by_file: dict[str, list[tuple[str, list[str]]]] = {}
    total = None
    for line in proc.stdout.splitlines():
        if "AUDIT|" in line:
            total = int(line.split("AUDIT|", 1)[1])
        elif "DECL|" in line:
            module_name, name, axiom_text = line.split("DECL|", 1)[1].split("|", 2)
            file = Path(*module_name.split(".")).with_suffix(".lean").as_posix()
            axioms = axiom_text.split(",") if axiom_text else []
            records_by_file.setdefault(file, []).append((name, axioms))

    if total is None or sum(map(len, records_by_file.values())) != total:
        sys.stderr.write("Lean axiom audit did not return its summary.\n")
        sys.stderr.write(proc.stdout)
        return 2

    show_all_results = bool(args.exact or (args.prefix and total <= 10))
    for file, file_records in sorted(records_by_file.items()):
        if args.by_file:
            file_axioms = sorted(
                {axiom for _, axioms in file_records for axiom in axioms}
            )
            result = ", ".join(file_axioms) if file_axioms else "no axiom dependencies"
            print(f"{file}: {result}")
            continue

        dependent_records = [(name, axioms) for name, axioms in file_records if axioms]
        print(f"{file}:")
        print(f"  declarations: {len(file_records)}")
        print(f"  axiom-dependent: {len(dependent_records)}")
        print(f"  axiom-free: {len(file_records) - len(dependent_records)}")

        if args.by_axiom:
            counts = Counter(axiom for _, axioms in dependent_records for axiom in axioms)
            if counts:
                print("  dependencies by axiom:")
                for axiom, count in sorted(counts.items()):
                    print(f"    {axiom}: {count}")

        if show_all_results:
            for name, axioms in file_records:
                result = ", ".join(axioms) if axioms else "axiom-free"
                print(f"  {name}: {result}")
            continue

        examples = dependent_records if args.all else dependent_records[: max(0, args.limit)]
        for name, axioms in examples:
            print(f"  {name}: {', '.join(axioms)}")
        if not args.all and len(dependent_records) > len(examples):
            remaining = len(dependent_records) - len(examples)
            print(f"  ... {remaining} more in this file; use --all to list them")

    has_dependencies = any(
        axioms for records in records_by_file.values() for _, axioms in records
    )
    if args.strict and has_dependencies:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
