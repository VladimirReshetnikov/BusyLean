#!/usr/bin/env python3
"""Clean-build the provided Lean source; never evaluate a contender.

Exit 0: definitions, proofs, audits, and timing budgets all passed.
Exit 1: compiler error, timeout, audit failure, or budget failure.
Exit 2: Lean unavailable or wrong version. An unexecuted check is never a pass.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
DEFS = ["BigNumber/Definitions", "BusyLean/Reflection", "BusyLean/Contender6",
        "Mirror/Model", "BusyLean/Contender7"]
PROOFS = ["Mirror/Compiler", "Mirror/Enumeration", "Mirror/Semantics",
          "Mirror/Bounds", "Mirror/Growth", "Mirror/Comparison"]
AUDITS = ["Mirror/Audit", "Mirror/Smoke"]

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", help="Path to the Lean 4.34.0 executable")
    args = parser.parse_args()
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    result: dict = {"status": "NOT_RUN", "expected_version": "4.34.0",
                    "kernel_checked": False, "budget_pass": None,
                    "records": [], "candidate_evaluated": False}
    log: list[str] = []
    def finish(code: int) -> int:
        (evidence / "lean_validation.json").write_text(
            json.dumps(result, indent=2) + "\n", encoding="utf-8")
        (evidence / "lean_validation.log").write_text(
            "\n".join(log) + "\n", encoding="utf-8")
        print(json.dumps(result, indent=2))
        return code
    lean = args.lean or shutil.which("lean")
    if lean is None:
        result["reason"] = "Lean executable is not installed or not on PATH."
        log.append(result["reason"])
        return finish(2)
    # Preserve argv[0] for elan's lean symlink; resolving it can invoke elan itself.
    lean = str(Path(lean).absolute())
    try:
        p = subprocess.run([lean, "--version"], cwd=ROOT / "lean",
                           text=True, capture_output=True, timeout=30)
        version = (p.stdout + p.stderr).strip()
        result["reported_version"] = version
        log.append(version)
        if p.returncode or not re.search(r"\b4\.34\.0\b", version):
            result["reason"] = "Lean 4.34.0 is required; version check failed."
            return finish(2)
    except (OSError, subprocess.TimeoutExpired) as exc:
        result["reason"] = f"Could not execute Lean: {exc}"
        log.append(result["reason"])
        return finish(2)
    build = ROOT / "lean" / ".check-build"
    if build.exists():
        shutil.rmtree(build)
    build.mkdir()
    env = os.environ.copy()
    env["LEAN_PATH"] = str(build)
    timings: dict[str, float] = {}
    try:
        for phase, modules in (("definitions", DEFS), ("proofs", PROOFS),
                               ("audits", AUDITS)):
            start_phase = time.perf_counter()
            for module in modules:
                target = build / (module + ".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                cmd = [lean, "-o", str(target), module + ".lean"]
                start = time.perf_counter()
                p = subprocess.run(cmd, cwd=ROOT / "lean", env=env,
                                   text=True, capture_output=True, timeout=180)
                elapsed = time.perf_counter() - start
                output = p.stdout + p.stderr
                log.extend([f"$ {' '.join(cmd)}", output,
                            f"elapsed_seconds={elapsed:.6f}"])
                result["records"].append({"module": module, "phase": phase,
                    "returncode": p.returncode, "seconds": elapsed})
                if p.returncode != 0 or "declaration uses 'sorry'" in output:
                    result.update(status="FAIL", reason=f"Failed module: {module}")
                    return finish(1)
            timings[phase] = time.perf_counter() - start_phase
    except (OSError, subprocess.TimeoutExpired) as exc:
        result.update(status="FAIL", reason=str(exc))
        log.append(str(exc))
        return finish(1)
    # Audit time is charged to the proof budget, conservatively.
    budgets_ok = timings["definitions"] <= 15 and (
        timings["proofs"] + timings["audits"]) <= 60
    result.update(status="PASS" if budgets_ok else "BUDGET_FAIL",
                  kernel_checked=True, budget_pass=budgets_ok, seconds=timings,
                  axiom_audit="PASS", dependency_audit="PASS")
    return finish(0 if budgets_ok else 1)

if __name__ == "__main__":
    sys.exit(main())
