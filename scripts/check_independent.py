#!/usr/bin/env python3
"""Clean-build the independent tower, check the time budgets, and audit it.

Usage (from the repository root):  python3 scripts/check_independent.py

Phases, starting from deleted build directories (the Lean core library is
precompiled, as the rules allow):

1. libraries: the generic modules the rungs are written in (the port of
   Contender 5's language, System F's untyped core and normalizer, and the
   ladder language with its strong normalization proof). They were accepted
   under their own budgets with the main tower, so this phase is reported but
   not budgeted.
2. definitions: the three rungs; budget 15 s.
3. proofs: the two comparisons and their lemmas; budget 60 s.

Then `test/IndependentAudit.lean` must run cleanly: every audited declaration
uses only the permitted axioms, and no rung's definition depends on a lower
rung or on a main-tower contender module.
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
LIBRARIES = ["BusyLean.Contender5", "BusyLean.SystemF.Normalize",
             "BusyLean.SystemFL.Ladder", "BusyLean.SystemFL.Church"]
DEFINITIONS = ["BusyLean.Independent.Ackermann", "BusyLean.Independent.SystemT",
               "BusyLean.Independent.Ladder"]
PROOFS = ["BusyLean.Independent.AckermannLtSystemT",
          "BusyLean.Independent.SystemTLtLadder"]
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
    note = f"(budget {budget:.0f} s)" if budget else "(library; not budgeted)"
    print(f"{label}: {elapsed:.1f} s {note}")
    if budget and elapsed > budget:
        sys.exit(f"FAIL: {label} exceed the budget")
    return elapsed


def main():
    for d in BUILD_DIRS:
        shutil.rmtree(d, ignore_errors=True)

    total = timed_build("libraries", LIBRARIES, None)
    total += timed_build("definitions", DEFINITIONS, DEFINITION_BUDGET)
    total += timed_build("proofs", PROOFS, PROOF_BUDGET)
    print(f"total clean build: {total:.1f} s")

    audit = run(["env", "lean", "test/IndependentAudit.lean"])
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
