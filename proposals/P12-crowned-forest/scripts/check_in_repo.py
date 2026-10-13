#!/usr/bin/env python3
"""Install and validate Contender 11 inside a BusyLean checkout.

This script performs the checks that cannot be run in the packaging container:
Lean elaboration, kernel checking, timing, axiom reporting, and transitive
closure hygiene.  It never evaluates a contender.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent.parent
PINNED_COMMIT = "4c4b03d0e2003c479e3bee90a21c8bea13f66c40"
PERMITTED_AXIOMS = {"propext", "Quot.sound"}


def run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)


def git_head(repo: Path) -> str | None:
    p = run(["git", "rev-parse", "HEAD"], repo)
    return p.stdout.strip() if p.returncode == 0 else None


def copy_candidate(repo: Path) -> list[str]:
    installed: list[str] = []
    for rel in ["BusyLean/Contender11.lean", "BusyLean/Comparison11.lean"]:
        src = PACKAGE / "candidate" / rel
        dst = repo / rel
        if dst.exists() and dst.read_bytes() != src.read_bytes():
            raise RuntimeError(f"refusing to overwrite differing file: {dst}")
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        installed.append(str(dst))
    return installed


def timed_lake(repo: Path, label: str, args: list[str], budget: float | None) -> dict[str, object]:
    start = time.monotonic()
    p = run(["lake", *args], repo)
    elapsed = time.monotonic() - start
    return {
        "label": label,
        "command": ["lake", *args],
        "returncode": p.returncode,
        "elapsed_seconds": elapsed,
        "budget_seconds": budget,
        "within_budget": budget is None or elapsed <= budget,
        "stdout": p.stdout,
        "stderr": p.stderr,
    }


def parse_axioms(text: str) -> dict[str, list[str]]:
    reports: dict[str, list[str]] = {}
    pattern = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)")
    for name, payload in pattern.findall(text):
        reports[name] = [x.strip() for x in payload.split(",") if x.strip()]
    return reports


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path, help="BusyLean checkout")
    ap.add_argument("--install", action="store_true", help="copy candidate modules into the checkout")
    ap.add_argument("--allow-different-head", action="store_true", help="allow a revision other than the pinned baseline")
    ap.add_argument("--report", type=Path, default=PACKAGE / "evidence" / "lean_validation.external.json")
    args = ap.parse_args()

    repo = args.repo.resolve()
    report: dict[str, object] = {
        "status": "not_run",
        "pinned_commit": PINNED_COMMIT,
        "repo": str(repo),
        "phases": [],
    }

    if not repo.is_dir():
        report["reason"] = "repository directory does not exist"
        args.report.write_text(json.dumps(report, indent=2), encoding="utf-8")
        print(json.dumps(report, indent=2))
        return 2
    if shutil.which("lake") is None:
        report["reason"] = "lake is not available on PATH"
        args.report.write_text(json.dumps(report, indent=2), encoding="utf-8")
        print(json.dumps(report, indent=2))
        return 2

    head = git_head(repo)
    report["observed_head"] = head
    if head != PINNED_COMMIT and not args.allow_different_head:
        report["reason"] = "checkout is not at the pinned baseline; pass --allow-different-head after review"
        args.report.write_text(json.dumps(report, indent=2), encoding="utf-8")
        print(json.dumps(report, indent=2))
        return 2

    if args.install:
        report["installed"] = copy_candidate(repo)
    else:
        missing = [str(repo / "BusyLean" / x) for x in ["Contender11.lean", "Comparison11.lean"]
                   if not (repo / "BusyLean" / x).exists()]
        if missing:
            report["reason"] = f"candidate modules are absent: {missing}; rerun with --install"
            args.report.write_text(json.dumps(report, indent=2), encoding="utf-8")
            print(json.dumps(report, indent=2))
            return 2

    version = run(["lake", "env", "lean", "--version"], repo)
    report["lean_version"] = (version.stdout + version.stderr).strip()

    phases = [
        timed_lake(repo, "previous contender", ["build", "BusyLean.Comparison10"], None),
        timed_lake(repo, "definitions", ["build", "BusyLean.Contender11"], 15.0),
        timed_lake(repo, "proofs", ["build", "BusyLean.Comparison11"], 60.0),
    ]
    report["phases"] = phases
    failed = any(p["returncode"] != 0 or not p["within_budget"] for p in phases)

    if not failed:
        smoke = timed_lake(
            repo,
            "smoke",
            ["env", "lean", str(PACKAGE / "candidate" / "test" / "Contender11Smoke.lean")],
            None,
        )
        audit = timed_lake(
            repo,
            "audit",
            ["env", "lean", str(PACKAGE / "candidate" / "test" / "Audit11.lean")],
            None,
        )
        report["smoke"] = smoke
        report["audit"] = audit
        failed = smoke["returncode"] != 0 or audit["returncode"] != 0
        audit_text = str(audit["stdout"]) + str(audit["stderr"])
        reports = parse_axioms(audit_text)
        report["axiom_reports"] = reports
        forbidden = {
            name: sorted(set(axs) - PERMITTED_AXIOMS)
            for name, axs in reports.items()
            if set(axs) - PERMITTED_AXIOMS
        }
        report["forbidden_axioms"] = forbidden
        if not reports or forbidden:
            failed = True

    report["status"] = "failed" if failed else "passed"
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
