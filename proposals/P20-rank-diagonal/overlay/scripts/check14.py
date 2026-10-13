#!/usr/bin/env python3
"""Build and audit the proposed BusyLean Contender 14.

Run from the BusyLean repository root after applying the overlay:
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
        sys.exit(f"FAIL: {label} build failed")
    note = f"(budget {budget:.0f} s)" if budget else "(accepted earlier)"
    print(f"{label}: {elapsed:.1f} s {note}")
    if budget is not None and elapsed > budget:
        sys.exit(f"FAIL: {label} exceeded the budget")
    return elapsed


def audit(path: str) -> int:
    result = run(["env", "lean", path])
    out = result.stdout + result.stderr
    print(out)
    if result.returncode != 0:
        sys.exit(f"FAIL: {path} did not run cleanly")
    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)", out
    )
    bad = [
        (name, axs)
        for name, axs in reports
        if axs and set(a.strip() for a in axs.split(",")) - PERMITTED
    ]
    if not reports or bad:
        sys.exit(f"FAIL: forbidden or missing axiom reports: {bad}")
    return len(reports)


def main() -> None:
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    total = timed_build("previous contender", PREVIOUS, None)
    total += timed_build("definitions", CURRENT_DEF, DEFINITION_BUDGET)
    total += timed_build("proofs", CURRENT_PROOF, PROOF_BUDGET)
    print(f"total clean build through Contender 14: {total:.1f} s")

    reports = audit("test/Audit.lean")
    reports += audit("test/Audit14.lean")
    print(
        f"PASS: {reports} declarations audited; axioms within "
        f"{sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
