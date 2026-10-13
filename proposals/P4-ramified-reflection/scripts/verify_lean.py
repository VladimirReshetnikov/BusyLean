#!/usr/bin/env python3
"""Cold-build and strict axiom/timing acceptance gate. Never evaluates the entries."""
from __future__ import annotations
import json, os, platform, re, shutil, subprocess, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
WORK=ROOT/'lean'
OUT=ROOT/'validation'
DEFS=['ListKit','Legacy','Language','Hierarchy','Contender']
PROOFS=['Baseline','Proofs','Audit','Smoke']
AUDIT=['Legacy.contender_5','contender_6','contender_5_lt_contender_6',
       'reflect_child_lt','reflect_boost_lt','finite_feedback_lt_grand',
       'boost_feedback_lt','high_level_lt_grand','input_lt_reflect']

# This lexer is only a preliminary source screen, not a security-certified parser.
def strip_comments_strings(text: str) -> str:
    ans=[]; i=0; nest=0; string=False
    while i<len(text):
        if nest:
            if text.startswith('/-',i): nest+=1; i+=2
            elif text.startswith('-/',i): nest-=1; i+=2
            else:
                ans.append('\n' if text[i]=='\n' else ' '); i+=1
        elif string:
            if text[i]=='\\': i+=2
            elif text[i]=='"': string=False; i+=1
            else: i+=1
        elif text.startswith('/-',i): nest=1; i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i); i=len(text) if j<0 else j
        elif text[i]=='"': string=True; i+=1
        else: ans.append(text[i]); i+=1
    return ''.join(ans)

def write_report(report: dict) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT/'lean_validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

def main() -> int:
    report={'target':'Lean 4.35.0','platform':platform.platform(),
            'definition_limit_seconds':15,'proof_limit_seconds':60,
            'kernel_checked':False,'timing_qualified':False}
    forbidden=re.compile(r'\b(axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|sorryAx|implemented_by|extern|trustCompiler|ofReduceBool)\b')
    findings=[]
    for p in sorted(WORK.rglob('*.lean')):
        findings += [f'{p.relative_to(WORK)}:{m.group(0)}'
                     for m in forbidden.finditer(strip_comments_strings(p.read_text()))]
    report['source_screen']={'status':'failed' if findings else 'passed', 'findings':findings,
                             'scope':'Token screen only, not an axiom audit'}
    if findings:
        report['status']='source_screen_failed'; write_report(report); return 1
    lean=shutil.which(os.environ.get('LEAN','lean'))
    if not lean:
        report['status']='not_run_compiler_unavailable'
        report['reason']='No lean, lake, or elan executable was available in the preparation container; toolchain download attempts also failed.'
        write_report(report); return 2
    try:
        ver=subprocess.run([lean,'--version'],cwd=WORK,text=True,capture_output=True,timeout=15)
    except (subprocess.TimeoutExpired,OSError) as exc:
        report['status']='toolchain_unavailable'; report['reason']=str(exc)
        write_report(report); return 2
    report['compiler_version']=ver.stdout.strip()
    if ver.returncode!=0 or '4.35.0' not in ver.stdout:
        report['status']='toolchain_mismatch'; report['stderr']=ver.stderr
        write_report(report); return 2
    # Remove only generated artifacts in this package's source directory.
    for ext in ('*.olean','*.ilean','*.olean.private','*.olean.server'):
        for p in WORK.rglob(ext): p.unlink()
    env=os.environ.copy()
    env['LEAN_PATH']=str(WORK)+(os.pathsep+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    phases=[]; audit=''
    for phase,modules,limit in [('definitions',DEFS,15),('proofs',PROOFS,60)]:
        start=time.perf_counter(); records=[]; log=[]; ok=True
        for mod in modules:
            remaining=limit-(time.perf_counter()-start)
            if remaining<=0:
                ok=False; log.append('PHASE TIMEOUT'); break
            cmd=[lean,'-o',f'BigNumber/{mod}.olean',f'BigNumber/{mod}.lean']
            try:
                t0=time.perf_counter()
                proc=subprocess.run(cmd,cwd=WORK,env=env,text=True,capture_output=True,timeout=remaining)
                records.append(dict(module=mod,seconds=time.perf_counter()-t0,returncode=proc.returncode))
                log += ['$ '+' '.join(cmd),proc.stdout,proc.stderr]
                if mod=='Audit': audit=proc.stdout+'\n'+proc.stderr
                if proc.returncode: ok=False; break
            except subprocess.TimeoutExpired:
                ok=False; log.append('PHASE TIMEOUT'); break
        elapsed=time.perf_counter()-start
        (OUT/f'lean_{phase}.log').write_text('\n'.join(log))
        phases.append(dict(name=phase,seconds=elapsed,limit_seconds=limit,passed=ok and elapsed<=limit,modules=records))
        if not ok:
            report.update(status='build_or_time_gate_failed',phases=phases)
            write_report(report); return 1
    missing=[]
    for short in AUDIT:
        name='BigNumber.'+short
        empty_text=f"'{name}' does not depend on any axioms"
        empty_list=re.search(re.escape(name)+r"['\"]?\s+depends on axioms:\s*\[\s*\]",audit)
        if empty_text not in audit and not empty_list: missing.append(name)
    report.update(phases=phases,axiom_audit={'passed':not missing,'missing_empty_results':missing})
    report['kernel_checked']=not missing
    report['timing_qualified']=not missing and all(x['passed'] for x in phases)
    report['status']='accepted_by_local_gate' if report['timing_qualified'] else 'axiom_audit_failed'
    write_report(report)
    return 0 if report['timing_qualified'] else 1

if __name__=='__main__': raise SystemExit(main())
