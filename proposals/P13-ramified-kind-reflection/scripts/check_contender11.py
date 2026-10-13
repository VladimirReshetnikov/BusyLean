#!/usr/bin/env python3
"""Clean-build and audit the proposed BusyLean Contender 11.

Copy this package's two Lean modules into the repository, add their imports to
BusyLean.lean, then run this script from the repository root.  It mirrors the
accepted `scripts/check.py` protocol while treating Contender 10 as the
precompiled previous entry.
"""
from __future__ import annotations

import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path.cwd()
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
    result = run(["build", *targets])
    elapsed = time.monotonic() - start
    if result.returncode != 0:
        print(result.stdout, result.stderr)
        raise SystemExit(f"FAIL: {label} build failed")
    note = f"(budget {budget:.0f} s)" if budget else "(accepted earlier)"
    print(f"{label}: {elapsed:.1f} s {note}")
    if budget is not None and elapsed > budget:
        raise SystemExit(f"FAIL: {label} exceeded the budget")
    return elapsed


def main() -> None:
    required = [
        ROOT / "BusyLean" / "Contender11.lean",
        ROOT / "BusyLean" / "Comparison11.lean",
        ROOT / "test" / "Contender11Audit.lean",
    ]
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        raise SystemExit("Missing integrated files:\n  " + "\n  ".join(missing))

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
        raise SystemExit(f"FAIL: forbidden axioms or missing reports: {bad}")
    print(
        f"PASS: {len(reports)} declarations audited; "
        f"axioms are within {sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
