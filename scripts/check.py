#!/usr/bin/env python3
"""Clean-build Contender 7, enforce the time budgets, and audit axioms.

Usage (from the repository root):  python3 scripts/check.py

Two timed phases, both beginning after both Lake build directories are removed
(the Lean core library is precompiled, as the rules allow):

1. definitions: `lake build BusyLean.Contender7`, which checks the new
   definition and everything it imports; budget 15 s;
2. proofs: the remaining full library, including `BusyLean.Comparison7`;
   budget 60 s.

Finally both the historical audit and the Contender 7 audit must run cleanly,
and every declaration reported by `#print axioms` must use only the permitted
axioms.
"""
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUILD_DIRS = [
    ROOT / ".lake" / "build",
    ROOT / "proposals" / "P5-w-reflection" / "lean" / ".lake" / "build",
]
PERMITTED = {"propext", "Quot.sound"}
DEFINITION_BUDGET = 15.0
PROOF_BUDGET = 60.0
LAKE = shutil.which("lake") or "lake"


def run(args):
    return subprocess.run([LAKE, *args], cwd=ROOT, capture_output=True, text=True)


def audit(path: str):
    result = run(["env", "lean", path])
    out = result.stdout + result.stderr
    print(f"--- {path} ---")
    print(out)
    if result.returncode != 0:
        sys.exit(f"FAIL: {path} did not run cleanly")
    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)", out
    )
    if not reports:
        sys.exit(f"FAIL: {path} produced no axiom reports")
    bad = [
        (name, axioms)
        for name, axioms in reports
        if axioms
        and set(a.strip() for a in axioms.split(",")) - PERMITTED
    ]
    if bad:
        sys.exit(f"FAIL: forbidden axioms in {path}: {bad}")
    return len(reports)


def main():
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    phases = [
        ("definitions", ["BusyLean.Contender7"], DEFINITION_BUDGET),
        ("proofs", [], PROOF_BUDGET),
    ]
    for label, target, budget in phases:
        start = time.monotonic()
        build = run(["build", *target])
        elapsed = time.monotonic() - start
        if build.returncode != 0:
            print(build.stdout, build.stderr)
            sys.exit(f"FAIL: {label} build failed")
        print(f"{label}: {elapsed:.2f} s (budget {budget:.0f} s)")
        if elapsed > budget:
            sys.exit(f"FAIL: {label} exceeded the budget")

    report_count = audit("test/Audit.lean")
    report_count += audit("test/Contender7Audit.lean")
    print(
        f"PASS: {report_count} declarations audited; "
        f"axioms within {sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
