#!/usr/bin/env python3
"""Reproducible kernel, timing, smoke, and axiom checks after integration."""
from __future__ import annotations

import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# When copied into the BusyLean repository, ROOT is the repository root.
if not (ROOT / "lakefile.toml").exists():
    candidate = ROOT / "repo_overlay"
    if (candidate / "BusyLean").exists():
        sys.exit(
            "Copy the overlay into a BusyLean checkout, then place this script "
            "under scripts/ and run it from there."
        )

BUILD_DIRS = [
    ROOT / ".lake" / "build",
    ROOT / "proposals" / "P5-w-reflection" / "lean" / ".lake" / "build",
]
PERMITTED = {"propext", "Quot.sound"}
DEFINITION_BUDGET = 15.0
PROOF_BUDGET = 60.0
LAKE = shutil.which("lake") or "lake"


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [LAKE, *args], cwd=ROOT, capture_output=True, text=True
    )


def timed(label: str, target: list[str], budget: float) -> None:
    start = time.monotonic()
    proc = run(["build", *target])
    elapsed = time.monotonic() - start
    if proc.returncode != 0:
        print(proc.stdout, proc.stderr)
        sys.exit(f"FAIL: {label} build failed")
    print(f"{label}: {elapsed:.1f} s (budget {budget:.0f} s)")
    if elapsed > budget:
        sys.exit(f"FAIL: {label} exceeded the budget")


def main() -> None:
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)

    timed("definitions", ["BusyLean.Contender7"], DEFINITION_BUDGET)
    timed("proofs", [], PROOF_BUDGET)

    smoke = run(["env", "lean", "test/MetaReflectionSmoke.lean"])
    print(smoke.stdout + smoke.stderr)
    if smoke.returncode != 0:
        sys.exit("FAIL: MetaReflectionSmoke did not run cleanly")

    audit = run(["env", "lean", "test/Contender7Audit.lean"])
    output = audit.stdout + audit.stderr
    print(output)
    if audit.returncode != 0:
        sys.exit("FAIL: Contender7Audit did not run cleanly")

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
        sys.exit(f"FAIL: forbidden axioms or missing reports: {bad}")

    print(
        f"PASS: {len(reports)} declarations audited; "
        f"axioms within {sorted(PERMITTED)}"
    )


if __name__ == "__main__":
    main()
