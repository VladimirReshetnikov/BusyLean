#!/usr/bin/env python3
"""Clean-build and audit BusyLean Contender 14.

Run from the BusyLean repository root after applying the overlay:
    python3 scripts/check_contender14.py
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
LAKE = shutil.which("lake") or "lake"
PREVIOUS = "BusyLean.Comparison13"
CURRENT_DEF = "BusyLean.Contender14"
CURRENT_PROOF = "BusyLean.Comparison14"
DEFINITION_BUDGET = 15.0
PROOF_BUDGET = 60.0
PERMITTED = {"propext", "Quot.sound"}
SOURCE_FILES = [
    ROOT / "BusyLean" / "HyperReflection.lean",
    ROOT / "BusyLean" / "HyperReflectionFacts.lean",
    ROOT / "BusyLean" / "Contender14.lean",
    ROOT / "BusyLean" / "Comparison14.lean",
]
FORBIDDEN = re.compile(
    r"\b(?:noncomputable|partial|unsafe|opaque|implemented_by|extern|"
    r"native_decide|sorryAx|Classical\.choice)\b"
)


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [LAKE, *args], cwd=ROOT, capture_output=True, text=True, check=False
    )


def build(label: str, target: str, budget: float | None) -> float:
    start = time.monotonic()
    proc = run(["build", target])
    elapsed = time.monotonic() - start
    if proc.returncode:
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=sys.stderr)
        raise SystemExit(f"FAIL: {label} build failed")
    note = f"budget {budget:.0f} s" if budget is not None else "accepted predecessor"
    print(f"{label}: {elapsed:.2f} s ({note})")
    if budget is not None and elapsed > budget:
        raise SystemExit(f"FAIL: {label} exceeded its budget")
    return elapsed


def source_guard() -> None:
    hits: list[str] = []
    for path in SOURCE_FILES:
        text = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(text.splitlines(), 1):
            if FORBIDDEN.search(line):
                hits.append(f"{path.relative_to(ROOT)}:{line_no}:{line.strip()}")
    if hits:
        raise SystemExit("FAIL: forbidden source constructs:\n" + "\n".join(hits))
    print("source guard: PASS")


def audit() -> None:
    proc = run(["env", "lean", "test/Contender14Audit.lean"])
    out = proc.stdout + proc.stderr
    print(out, end="")
    if proc.returncode:
        raise SystemExit("FAIL: Lean audit failed")
    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)", out
    )
    bad = []
    for name, raw in reports:
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        extra = axioms - PERMITTED
        if extra:
            bad.append((name, sorted(extra)))
    if not reports or bad:
        raise SystemExit(f"FAIL: axiom audit failed: {bad}")
    if "avoids all 9 forbidden names" not in out:
        raise SystemExit("FAIL: closure audit output was not found")
    print(f"audit: PASS ({len(reports)} declarations, allowed axioms only)")


def main() -> None:
    for directory in BUILD_DIRS:
        shutil.rmtree(directory, ignore_errors=True)
    build("previous contender", PREVIOUS, None)
    build("definitions", CURRENT_DEF, DEFINITION_BUDGET)
    build("proofs", CURRENT_PROOF, PROOF_BUDGET)
    source_guard()
    audit()
    print("Contender 14 validation: PASS")


if __name__ == "__main__":
    main()
