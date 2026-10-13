#!/usr/bin/env python3
"""Rebuild every delivered Lean module and audit it without evaluating the entry.

Only Python's standard library and the pinned Lean 4.19.0 are required.
Project imports are rebuilt in a fresh temporary directory; the installed
Lean standard library is used in its normal compiled form.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
MODULES = [
    "Original", "Trees", "Reflection", "Hierarchy", "Arboreal", "Forest",
    "Preliminary", "ForestHierarchy", "Contender", "Smoke", "Audit",
]
ENTRY_MODULES = {
    "Original", "Trees", "Hierarchy", "Arboreal", "Forest",
    "Preliminary", "ForestHierarchy", "Contender",
}


def run(command, *, cwd, env, timeout=60):
    started = time.perf_counter()
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=timeout, check=False)
    elapsed = time.perf_counter() - started
    return result, elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--output", type=Path, default=ROOT / "validation" / "build_report.json")
    args = parser.parse_args()
    lean = shutil.which(args.lean) or args.lean
    env = os.environ.copy()
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    if "version 4.19.0," not in version:
        raise SystemExit(f"Expected Lean 4.19.0; found {version}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report = {
        "status": "RUNNING", "lean_version": version,
        "platform": platform.platform(), "machine": platform.machine(),
        "python_version": platform.python_version(),
        "method": "Fresh temporary project; each source checked and compiled; installed standard library reused.",
        "entry_evaluated": False, "contender5_evaluated": False,
        "modules": [], "audit": {},
    }
    logs = []
    with tempfile.TemporaryDirectory(prefix="lean-reflection-verify-") as temp:
        build = Path(temp)
        env["LEAN_PATH"] = str(build)
        for module in MODULES:
            shutil.copy2(ROOT / "lean" / f"{module}.lean", build / f"{module}.lean")
        all_started = time.perf_counter()
        for module in MODULES:
            source = build / f"{module}.lean"
            result, elapsed = run([lean, "-o", f"{module}.olean", source.name],
                                  cwd=build, env=env)
            logs.append(f"MODULE {module}\n{result.stdout}")
            row = {"module": module, "seconds": round(elapsed, 6),
                   "exit_code": result.returncode,
                   "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            report["modules"].append(row)
            if result.returncode:
                report["status"] = "FAIL"
                report["failure"] = module
                args.output.write_text(json.dumps(report, indent=2) + "\n")
                (args.output.parent / "lean_build.log").write_text("\n".join(logs))
                raise SystemExit(result.stdout)
            if module == "Audit":
                output = result.stdout
                clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
                unclean = [line for line in output.splitlines()
                           if "depends on axioms" in line]
                targets = len(re.findall(r"^#print axioms ", source.read_text(), re.M))
                report["audit"] = {"targets": targets, "empty_axiom_lists": len(clean),
                                   "nonempty_axiom_reports": unclean,
                                   "all_empty": len(clean) == targets and not unclean}
                if not report["audit"]["all_empty"]:
                    raise SystemExit("Axiom audit failed or incomplete: " + output)
        report["all_modules_wall_seconds"] = round(time.perf_counter() - all_started, 6)
        report["entry_dependency_seconds"] = round(sum(
            row["seconds"] for row in report["modules"] if row["module"] in ENTRY_MODULES), 6)
        report["all_modules_sum_seconds"] = round(sum(row["seconds"] for row in report["modules"]), 6)

        # Read-only validation of the elaborated dependency graph.
        dependency_source = ROOT / "validation" / "DependencyAudit.lean"
        if dependency_source.exists():
            shutil.copy2(dependency_source, build / dependency_source.name)
            result, elapsed = run([lean, dependency_source.name], cwd=build, env=env)
            logs.append(f"DEPENDENCY AUDIT\n{result.stdout}")
            report["dependency_audit"] = {"exit_code": result.returncode,
                "seconds": round(elapsed, 6), "output": result.stdout.strip()}
            if result.returncode:
                raise SystemExit(result.stdout)

        # Independent finite semantics comparison, not a cross-prover theorem.
        source_check = ROOT / "validation" / "source_reference.py"
        cross_output = args.output.parent / "source_crosscheck.json"
        if source_check.exists():
            result, elapsed = run([shutil.which("python3") or "python3", str(source_check),
                "--lean", lean, "--olean-path", str(build),
                "--output", str(cross_output)], cwd=ROOT, env=env)
            logs.append(f"SOURCE CROSS-CHECK\n{result.stdout}")
            report["source_crosscheck_seconds"] = round(elapsed, 6)
            if result.returncode:
                raise SystemExit(result.stdout)
            report["source_crosscheck"] = json.loads(cross_output.read_text())

    report["status"] = "PASS"
    report["entry_under_15_seconds_here"] = report["entry_dependency_seconds"] < 15
    report["all_sources_and_audits_under_60_seconds_here"] = report["all_modules_wall_seconds"] < 60
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    (args.output.parent / "lean_build.log").write_text("\n".join(logs))
    print(json.dumps({
        "status": report["status"],
        "entry_dependency_seconds": report["entry_dependency_seconds"],
        "all_modules_wall_seconds": report["all_modules_wall_seconds"],
        "axiom_audit": report["audit"],
        "source_term_values_compared": report.get("source_crosscheck", {}).get("term_values_compared"),
    }, indent=2))


if __name__ == "__main__":
    main()
