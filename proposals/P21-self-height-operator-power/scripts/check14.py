#!/usr/bin/env python3
"""Clean-build and audit the Contender 14 overlay.

Copy BusyLean/Contender14.lean, BusyLean/Comparison14.lean and
 test/Audit14.lean into a checkout of BusyLean, then run from the repository
root:

    python3 scripts/check14.py
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
PREVIOUS = "BusyLean.Comparison13"
CURRENT_DEF = "BusyLean.Contender14"
CURRENT_PROOF = "BusyLean.Comparison14"
DEFINITION_BUDGET = 15.0
PROOF_BUDGET = 60.0
LAKE = shutil.which("lake")


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    if LAKE is None:
        raise SystemExit(
            "FAIL: `lake` was not found. Install the repository-pinned "
            "Lean toolchain before running this audit."
        )
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
    suffix = f"budget {budget:.0f} s" if budget else "accepted earlier"
    print(f"{label}: {elapsed:.2f} s ({suffix})")
    if budget is not None and elapsed > budget:
        raise SystemExit(f"FAIL: {label} exceeded its budget")
    return elapsed


def main() -> None:
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    total = timed_build("previous contender", [PREVIOUS], None)
    total += timed_build("definitions", [CURRENT_DEF], DEFINITION_BUDGET)
    total += timed_build("proofs", [CURRENT_PROOF], PROOF_BUDGET)
    print(f"total clean build: {total:.2f} s")

    audit = run(["env", "lean", "test/Audit14.lean"])
    output = audit.stdout + audit.stderr
    print(output)
    if audit.returncode != 0:
        raise SystemExit("FAIL: audit did not run cleanly")

    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)",
        output,
    )
    bad = [
        (name, axioms)
        for name, axioms in reports
        if axioms
        and set(a.strip() for a in axioms.split(",")) - PERMITTED
    ]
    if not reports or bad:
        raise SystemExit(f"FAIL: forbidden axioms or no reports: {bad}")
    print(
        f"PASS: {len(reports)} declarations audited; "
        f"axioms within {sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
