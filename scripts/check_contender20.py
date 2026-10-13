#!/usr/bin/env python3
"""Clean-build and audit the proposed BusyLean Contender 20.

Run from the BusyLean repository root after copying the proposal modules into
place:

    python3 scripts/check_contender20.py

The previous accepted contender is prebuilt and treated like an existing
library. Only the incremental definition and proof phases are compared with
the repository's 15 s / 60 s contest budgets.
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
        print(build.stdout, build.stderr, sep="\n", file=sys.stderr)
        raise SystemExit(f"FAIL: {label} build failed")
    note = (
        f"(budget {budget:.0f} s)"
        if budget is not None
        else "(accepted earlier; not budgeted)"
    )
    print(f"{label}: {elapsed:.3f} s {note}")
    if budget is not None and elapsed > budget:
        raise SystemExit(f"FAIL: {label} exceeded the budget")
    return elapsed


def run_lean(path: str) -> str:
    proc = run(["env", "lean", path])
    out = proc.stdout + proc.stderr
    print(out)
    if proc.returncode != 0:
        raise SystemExit(f"FAIL: {path} did not run cleanly")
    return out


def main() -> None:
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    total = timed_build("previous contender", PREVIOUS, None)
    total += timed_build("Contender 20 definitions", CURRENT_DEF, DEFINITION_BUDGET)
    total += timed_build("Contender 20 proofs", CURRENT_PROOF, PROOF_BUDGET)
    print(f"total clean build: {total:.3f} s")

    run_lean("test/WTreeLadderSmoke.lean")
    audit = run_lean("test/Contender20Audit.lean")
    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)", audit
    )
    bad = [
        (name, axioms)
        for name, axioms in reports
        if axioms
        and {a.strip() for a in axioms.split(",")} - PERMITTED
    ]
    if not reports:
        raise SystemExit("FAIL: the axiom audit printed no declarations")
    if bad:
        raise SystemExit(f"FAIL: forbidden axioms: {bad}")
    print(
        f"PASS: {len(reports)} declarations audited; "
        f"axioms within {sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
