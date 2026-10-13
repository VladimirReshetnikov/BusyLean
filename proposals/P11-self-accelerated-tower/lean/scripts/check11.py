#!/usr/bin/env python3
"""Build and audit the proposed BusyLean Contender 11.

Copy the package's `BusyLean/*.lean` files and `test/Contender11Audit.lean` into
the BusyLean repository, then run this script from the repository root.
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


def timed_build(label: str, targets: list[str], budget: float | None) -> float:
    start = time.monotonic()
    build = run(["build", *targets])
    elapsed = time.monotonic() - start
    if build.returncode != 0:
        print(build.stdout, build.stderr)
        sys.exit(f"FAIL: {label} build failed")
    note = (
        f"(budget {budget:.0f} s)"
        if budget is not None
        else "(accepted earlier; not budgeted)"
    )
    print(f"{label}: {elapsed:.1f} s {note}")
    if budget is not None and elapsed > budget:
        sys.exit(f"FAIL: {label} exceeded the budget")
    return elapsed


def main() -> None:
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    total = timed_build("previous contender", [PREVIOUS], None)
    total += timed_build("definitions", [CURRENT_DEF], DEFINITION_BUDGET)
    total += timed_build("proofs", [CURRENT_PROOF], PROOF_BUDGET)
    print(f"total clean build: {total:.1f} s")

    audit = run(["env", "lean", "test/Contender11Audit.lean"])
    output = audit.stdout + audit.stderr
    print(output)
    if audit.returncode != 0:
        sys.exit("FAIL: Contender 11 audit did not run cleanly")

    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)",
        output,
    )
    bad = [
        (name, axioms)
        for name, axioms in reports
        if axioms
        and set(axiom.strip() for axiom in axioms.split(",")) - PERMITTED
    ]
    if not reports or bad:
        sys.exit(f"FAIL: forbidden axioms or missing reports: {bad}")
    print(
        f"PASS: {len(reports)} declarations audited; "
        f"axioms within {sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
