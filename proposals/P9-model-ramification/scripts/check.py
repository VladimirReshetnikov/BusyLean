#!/usr/bin/env python3
"""Clean Lean build, timing, smoke tests, and axiom/dependency audit.

Requires an already installed Lean 4.34.0 toolchain. Does not evaluate C6/C7.
A missing toolchain is NOT a passing result. Artifacts are kept in evidence/.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT/'lean'
EVIDENCE = ROOT/'evidence'
EXPECTED = '4.34.0'

def run(command: list[str], log_name: str, timeout: int = 180) -> dict:
    start = time.perf_counter()
    try:
        p = subprocess.run(command, cwd=PROJECT, capture_output=True, text=True,
                           timeout=timeout, check=False)
        text = p.stdout + p.stderr
        code = p.returncode
    except subprocess.TimeoutExpired as exc:
        text = 'PROCESS TIMEOUT\n' + str(exc.stdout or '') + str(exc.stderr or '')
        code = 124
    (EVIDENCE/log_name).write_text(text)
    return {'command': command, 'returncode': code,
            'seconds': round(time.perf_counter()-start, 3), 'log': log_name}

def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    lake = shutil.which('lake')
    if not lake:
        report = {'status': 'not_run', 'reason': 'lake/Lean toolchain unavailable',
                  'kernel_checked': False, 'budget_compliance': 'unverified',
                  'required_toolchain': 'leanprover/lean4:v4.34.0'}
        (EVIDENCE/'lean_validation.json').write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(report, indent=2))
        return 2
    version = run([lake, 'env', 'lean', '--version'], 'lean_version.log', 30)
    version_text = (EVIDENCE/'lean_version.log').read_text()
    if version['returncode'] or EXPECTED not in version_text:
        report = {'status':'not_run', 'reason':'required toolchain not confirmed',
                  'kernel_checked': False, 'version_probe':version}
        (EVIDENCE/'lean_validation.json').write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(report, indent=2)); return 2
    shutil.rmtree(PROJECT/'.lake/build', ignore_errors=True)
    phases = []
    for command, log, limit in [
        ([lake,'build','+BusyLean7.Definitions'], 'lean_definitions.log', 180),
        ([lake,'build','BusyLean7'], 'lean_proofs.log', 180),
        ([lake,'env','lean','../test/Smoke.lean'], 'lean_smoke.log', 60),
        ([lake,'env','lean','../test/Audit.lean'], 'lean_audit.log', 60)]:
        phase = run(command, log, limit)
        phases.append(phase)
        if phase['returncode']:
            break
    success = len(phases)==4 and all(p['returncode']==0 for p in phases)
    axiom_lists = []
    if success:
        text = (EVIDENCE/'lean_audit.log').read_text()
        for body in re.findall(r'depends on axioms:\s*\[([^]]*)\]', text):
            axiom_lists.append([s.strip() for s in body.split(',') if s.strip()])
        for _ in re.findall(r'does not depend on any axioms', text):
            axiom_lists.append([])
        success = len(axiom_lists)>=5 and all(
            set(xs) <= {'propext','Quot.sound'} for xs in axiom_lists)
    budgets = success and phases[0]['seconds']<=15 and phases[1]['seconds']<=60
    report = {'status':'passed' if success and budgets else 'failed', 'kernel_checked':success,
              'phases':phases, 'axiom_lists':axiom_lists,
              'budget_compliance':budgets, 'definition_budget_seconds':15,
              'proof_budget_seconds':60, 'evaluated_contenders':False}
    (EVIDENCE/'lean_validation.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return 0 if success and budgets else 1

if __name__ == '__main__':
    raise SystemExit(main())
