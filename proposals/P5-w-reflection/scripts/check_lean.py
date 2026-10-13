#!/usr/bin/env python3
"""Compile and time the two contest gates; fail closed if Lean is missing.

Definition time includes loading prebuilt Init and producing the definition
module. Proof time includes importing that module. No target number is evaluated.
Use the pinned native toolchain; WASM times are not contest-equivalent.
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT/'evidence/lean_validation.json')
    args = parser.parse_args()
    lean = shutil.which('lean')
    report: dict = {'required_toolchain': 'leanprover/lean4:v4.19.0',
                    'definitions_limit_seconds': 15, 'proof_limit_seconds': 60,
                    'kernel_checked': False, 'timing_verified': False, 'runs': []}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if lean is None:
        report.update(status='not_run', reason='Lean executable not installed in this runtime')
        args.output.write_text(json.dumps(report, indent=2)+'\n')
        print(report['reason'], file=sys.stderr)
        return 2
    env = dict(os.environ)
    env['LEAN_PATH'] = str(ROOT/'lean')
    version = subprocess.run([lean, '--version'], cwd=ROOT/'lean', env=env,
                             capture_output=True, text=True)
    report['version'] = version.stdout.strip()
    if version.returncode or 'version 4.19.0' not in version.stdout:
        report.update(status='wrong_version', reason='Pinned Lean 4.19.0 is required')
        args.output.write_text(json.dumps(report, indent=2)+'\n')
        return 2
    jobs = [(['-o', 'BigNumber/Definitions.olean', 'BigNumber/Definitions.lean'], 15),
            (['-o', 'BigNumber/Proofs.olean', 'BigNumber/Proofs.lean'], 60),
            (['BigNumber/Audit.lean'], 60)]
    all_ok, timing_ok, audit_ok = True, True, False
    for argv, limit in jobs:
        start = time.perf_counter()
        try:
            proc = subprocess.run([lean, *argv], cwd=ROOT/'lean', env=env,
                                  capture_output=True, text=True, timeout=120)
            row = {'arguments': argv, 'elapsed_seconds': time.perf_counter()-start,
                   'returncode': proc.returncode, 'stdout': proc.stdout, 'stderr': proc.stderr}
        except subprocess.TimeoutExpired:
            row = {'arguments': argv, 'elapsed_seconds': time.perf_counter()-start,
                   'returncode': None, 'error': '120-second safety timeout'}
        report['runs'].append(row)
        if row['returncode'] != 0:
            all_ok = False
            break
        timing_ok &= row['elapsed_seconds'] <= limit
        if argv == jobs[-1][0]:
            out = row['stdout']
            # A new output format requires manual inspection, not an automatic pass.
            audit_ok = out.count('does not depend on any axioms') == 2
            report['empty_axiom_audit'] = audit_ok
    report.update(kernel_checked=all_ok, timing_verified=all_ok and timing_ok,
                  status='passed' if all_ok and timing_ok and audit_ok else 'failed_or_needs_review')
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return 0 if report['status'] == 'passed' else 1

if __name__ == '__main__':
    raise SystemExit(main())
