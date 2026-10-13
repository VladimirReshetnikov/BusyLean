#!/usr/bin/env python3
"""Clean-build the contest entries, check the time budgets, and audit axioms.

Usage (from the repository root):  python3 scripts/check.py

Phases, starting from deleted build directories (the Lean core library is
precompiled, as the rules allow):

1. previous contender: build the previous contender's definition and proof
   modules. They were accepted under their own budgets, so this phase is
   reported but not budgeted, like the precompiled core library.
2. definitions: time the build of the current contender's definition module
   (`CURRENT_DEF`) on top of phase 1; budget 15 s.
3. proofs: time the remaining modules (the comparison theorems and the rest
   of the library); budget 60 s.

Then every audited declaration must use only the permitted axioms. The total
clean-build time is reported too.
"""
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUILD_DIRS = [ROOT / ".lake" / "build",
              ROOT / "proposals" / "P5-w-reflection" / "lean" / ".lake" / "build"]
PERMITTED = {"propext", "Quot.sound"}
PREVIOUS = "BusyLean.Comparison36"   # previous contender: definitions + proofs
CURRENT_DEF = "BusyLean.Contender37"  # current contender's definition module
DEFINITION_BUDGET = 15.0  # seconds
PROOF_BUDGET = 60.0
LAKE = shutil.which("lake") or "lake"


def run(args):
    return subprocess.run([LAKE, *args], cwd=ROOT, capture_output=True, text=True)


def timed_build(label, target, budget):
    start = time.monotonic()
    build = run(["build", *target])
    elapsed = time.monotonic() - start
    if build.returncode != 0:
        print(build.stdout, build.stderr)
        sys.exit(f"FAIL: {label} build failed")
    note = f"(budget {budget:.0f} s)" if budget else "(accepted earlier; not budgeted)"
    print(f"{label}: {elapsed:.1f} s {note}")
    if budget and elapsed > budget:
        sys.exit(f"FAIL: {label} exceed the budget")
    return elapsed


def main():
    for d in BUILD_DIRS:
        shutil.rmtree(d, ignore_errors=True)

    total = timed_build("previous contender", [PREVIOUS], None)
    total += timed_build("definitions", [CURRENT_DEF], DEFINITION_BUDGET)
    total += timed_build("proofs", [], PROOF_BUDGET)
    print(f"total clean build: {total:.1f} s")

    audit = run(["env", "lean", "test/Audit.lean"])
    out = audit.stdout + audit.stderr
    print(out)
    if audit.returncode != 0:
        sys.exit("FAIL: audit did not run cleanly")
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)", out)
    bad = [(name, axs) for name, axs in reports
           if axs and set(a.strip() for a in axs.split(",")) - PERMITTED]
    if not reports or bad:
        sys.exit(f"FAIL: forbidden axioms: {bad}")
    print(f"PASS: {len(reports)} declarations audited, axioms within {sorted(PERMITTED)}")


if __name__ == "__main__":
    main()
