#!/usr/bin/env python3
"""Clean-build and audit the Contender 20 proposal.

Run from an installed BusyLean checkout:

    python3 scripts/check20.py

The accepted Contender 19 stack is built first and is not charged to the new
entry.  The new definition and proof phases are checked against the repository's
15 s / 60 s budgets.  Then the focused kernel audit is run and every printed
axiom set is restricted to propext and Quot.sound.
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
PREVIOUS = "BusyLean.Comparison19"
CURRENT_DEF = "BusyLean.Contender20"
CURRENT_PROOF = "BusyLean.Comparison20"
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
        print(build.stdout, build.stderr)
        raise SystemExit(f"FAIL: {label} build failed")
    note = (
        f"(budget {budget:.0f} s)"
        if budget is not None
        else "(accepted earlier; not budgeted)"
    )
    print(f"{label}: {elapsed:.1f} s {note}")
    if budget is not None and elapsed > budget:
        raise SystemExit(f"FAIL: {label} exceeded the budget")
    return elapsed


def main() -> None:
    if shutil.which("lake") is None:
        raise SystemExit("FAIL: lake is not on PATH")

    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    total = timed_build("previous contender", PREVIOUS, None)
    total += timed_build("definitions", CURRENT_DEF, DEFINITION_BUDGET)
    total += timed_build("proofs", CURRENT_PROOF, PROOF_BUDGET)
    print(f"total clean build: {total:.1f} s")

    audit = run(["env", "lean", "test/Audit20.lean"])
    output = audit.stdout + audit.stderr
    print(output)
    if audit.returncode != 0:
        raise SystemExit("FAIL: focused audit did not run cleanly")

    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)",
        output,
    )
    bad = [
        (name, axioms)
        for name, axioms in reports
        if axioms
        and set(item.strip() for item in axioms.split(",")) - PERMITTED
    ]
    if not reports:
        raise SystemExit("FAIL: no #print axioms reports were detected")
    if bad:
        raise SystemExit(f"FAIL: forbidden axioms: {bad}")

    print(
        "PASS: "
        f"{len(reports)} declarations audited; axioms within {sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
