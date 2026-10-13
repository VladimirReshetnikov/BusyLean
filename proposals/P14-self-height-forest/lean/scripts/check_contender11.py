#!/usr/bin/env python3
"""Clean-build Contender 11, enforce BusyLean budgets, and audit axioms.

Copy this file to `scripts/check_contender11.py` in the pinned BusyLean checkout,
copy `Contender11.lean`, `Comparison11.lean`, and `Audit11.lean` to their stated
locations, update `BusyLean.lean`, then run:

    python3 scripts/check_contender11.py
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
        raise SystemExit(f"FAIL: {label} build failed")
    note = f"(budget {budget:.0f} s)" if budget else "(accepted earlier; not budgeted)"
    print(f"{label}: {elapsed:.1f} s {note}")
    if budget is not None and elapsed > budget:
        raise SystemExit(f"FAIL: {label} exceeded the budget")
    return elapsed


def main() -> None:
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    total = timed_build("previous contender", [PREVIOUS], None)
    total += timed_build("definitions", [CURRENT_DEF], DEFINITION_BUDGET)
    total += timed_build("proofs", [], PROOF_BUDGET)
    print(f"total clean build: {total:.1f} s")

    audit = run(["env", "lean", "test/Audit11.lean"])
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
        if axioms and {a.strip() for a in axioms.split(",")} - PERMITTED
    ]
    if not reports or bad:
        raise SystemExit(f"FAIL: forbidden axioms: {bad}")

    print(
        f"PASS: {len(reports)} declarations audited; "
        f"axioms within {sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
