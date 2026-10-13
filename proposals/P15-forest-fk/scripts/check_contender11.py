#!/usr/bin/env python3
"""Clean-build and audit BusyLean Contender 11 after integration.

Run from the BusyLean repository root after copying the supplied Lean modules:

    python3 scripts/check_contender11.py

The previous contender is built first and treated as precompiled history.  The
new definition and proof phases are then timed against BusyLean's 15 s / 60 s
budgets.  Finally the standalone audit checks axioms and dependency hygiene.
"""
from __future__ import annotations

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
PREVIOUS = "BusyLean.Comparison10"
CURRENT_DEF = "BusyLean.Contender11"
CURRENT_PROOF = "BusyLean.Comparison11"
DEFINITION_BUDGET = 15.0
PROOF_BUDGET = 60.0
LAKE = shutil.which("lake") or "lake"


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [LAKE, *args], cwd=ROOT, capture_output=True, text=True, check=False
    )


def timed_build(label: str, target: str, budget: float | None) -> float:
    start = time.monotonic()
    build = run(["build", target])
    elapsed = time.monotonic() - start
    if build.returncode != 0:
        print(build.stdout)
        print(build.stderr, file=sys.stderr)
        raise SystemExit(f"FAIL: {label} build failed")
    note = f"(budget {budget:.0f} s)" if budget else "(accepted history; not budgeted)"
    print(f"{label}: {elapsed:.2f} s {note}")
    if budget is not None and elapsed > budget:
        raise SystemExit(f"FAIL: {label} exceeded the budget")
    return elapsed


def main() -> None:
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    total = timed_build("previous contender", PREVIOUS, None)
    total += timed_build("Contender 11 definitions", CURRENT_DEF, DEFINITION_BUDGET)
    total += timed_build("Contender 11 proofs", CURRENT_PROOF, PROOF_BUDGET)
    print(f"total staged clean build: {total:.2f} s")

    audit = run(["env", "lean", "test/Contender11Audit.lean"])
    output = audit.stdout + audit.stderr
    print(output)
    if audit.returncode != 0:
        raise SystemExit("FAIL: Contender 11 audit did not run cleanly")

    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)", output
    )
    bad = [
        (name, axioms)
        for name, axioms in reports
        if axioms
        and {axiom.strip() for axiom in axioms.split(",")} - PERMITTED
    ]
    if not reports:
        raise SystemExit("FAIL: no axiom reports were found")
    if bad:
        raise SystemExit(f"FAIL: forbidden axioms: {bad}")
    print(
        f"PASS: {len(reports)} declarations audited; axioms are within "
        f"{sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
