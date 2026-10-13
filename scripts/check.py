#!/usr/bin/env python3
"""Clean-build the contest entry, check the time budgets, and audit axioms.

Usage (from the repository root):  python3 scripts/check.py

Two timed phases, both from a clean build directory (the Lean core library is
precompiled, as the rules allow):

1. definitions: `lake build BusyLean.Contender6`, which checks the definition
   of `contender_6` and everything it imports (P5's definitions included);
   budget 15 s;
2. proofs: the remaining modules (the Contender 5 port, the port-agreement
   proof, all comparison theorems); budget 60 s.

Then every audited declaration must use only the permitted axioms.
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
DEFINITION_BUDGET = 15.0  # seconds
PROOF_BUDGET = 60.0
LAKE = shutil.which("lake") or "lake"


def run(args):
    return subprocess.run([LAKE, *args], cwd=ROOT, capture_output=True, text=True)


def main():
    for d in BUILD_DIRS:
        shutil.rmtree(d, ignore_errors=True)

    for label, target, budget in [("definitions", ["BusyLean.Contender6"], DEFINITION_BUDGET),
                                  ("proofs", [], PROOF_BUDGET)]:
        start = time.monotonic()
        build = run(["build", *target])
        elapsed = time.monotonic() - start
        if build.returncode != 0:
            print(build.stdout, build.stderr)
            sys.exit(f"FAIL: {label} build failed")
        print(f"{label}: {elapsed:.1f} s (budget {budget:.0f} s)")
        if elapsed > budget:
            sys.exit(f"FAIL: {label} exceed the budget")

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
