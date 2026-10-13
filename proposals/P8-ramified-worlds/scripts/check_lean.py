#!/usr/bin/env python3
"""Clean-build and audit the proposal. Never evaluates a large number.

Download/update dependencies before timing. The definition phase includes all
imported non-core Lean modules. The proof phase is incremental from those
checked definitions. Audit/Smoke are separate. JSON records failures honestly.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "lean"
OUT = ROOT / "audit"

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-update", action="store_true")
    ap.add_argument("--no-budgets", action="store_true")
    args = ap.parse_args()
    OUT.mkdir(exist_ok=True)
    record = {"toolchain": (PROJECT / "lean-toolchain").read_text().strip(),
              "status": "not_run", "phases": [],
              "definition_budget_seconds": 15, "proof_budget_seconds": 60}
    def save():
        (OUT / "lean-validation.json").write_text(json.dumps(record, indent=2) + "\n")
    lake = shutil.which("lake")
    if lake is None:
        record.update(status="unavailable", reason="No lake/Lean executable is installed")
        save()
        print(record["reason"], file=sys.stderr)
        return 2
    if not args.skip_update:
        result = subprocess.run([lake, "update"], cwd=PROJECT, capture_output=True, text=True)
        (OUT / "lake-update.txt").write_text(result.stdout + result.stderr)
        if result.returncode:
            record.update(status="dependency_failure", returncode=result.returncode)
            save()
            return 1
    # Remove local and dependency compilation output, preserving source and
    # the core installation. Also cover the upstream nested local P5 project.
    build_dirs = list(PROJECT.rglob(".lake/build"))
    for path in sorted(build_dirs, key=lambda p: len(p.parts), reverse=True):
        if path.is_dir():
            shutil.rmtree(path)
    phases = [
        ("definitions", [lake, "build", "BusyLeanNext.Definitions"], 15),
        ("proofs", [lake, "build", "BusyLeanNext.Proofs"], 60),
        ("root", [lake, "build", "BusyLeanNext"], 60),
        ("audit", [lake, "env", "lean", "test/Audit.lean"], 60),
        ("smoke", [lake, "env", "lean", "test/Smoke.lean"], 60),
    ]
    for name, cmd, budget in phases:
        start = time.perf_counter()
        try:
            r = subprocess.run(cmd, cwd=PROJECT, capture_output=True, text=True,
                               timeout=None if args.no_budgets else budget)
            elapsed = time.perf_counter() - start
            (OUT / f"lean-{name}.txt").write_text(r.stdout + r.stderr)
            item = {"name": name, "seconds": elapsed, "returncode": r.returncode,
                    "budget_seconds": budget, "status": "pass" if r.returncode == 0 else "fail"}
        except subprocess.TimeoutExpired as exc:
            elapsed = time.perf_counter() - start
            def text(x):
                return x.decode(errors="replace") if isinstance(x, bytes) else (x or "")
            (OUT / f"lean-{name}.txt").write_text(text(exc.stdout) + text(exc.stderr))
            item = {"name": name, "seconds": elapsed, "budget_seconds": budget,
                    "status": "timeout"}
        record["phases"].append(item)
        save()
        if item["status"] != "pass":
            record["status"] = "failed"
            save()
            return 1
    record["status"] = "passed_with_budgets" if not args.no_budgets else "passed_without_budgets"
    save()
    print(json.dumps(record, indent=2))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
