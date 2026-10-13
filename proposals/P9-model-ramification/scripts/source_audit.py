#!/usr/bin/env python3
"""Lexical checks only; this is explicitly NOT a Lean parser or kernel audit."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def strip_comments_strings(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2
            elif text.startswith('-/', i):
                depth -= 1; i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; i += 2
        elif text.startswith('--', i):
            stop = text.find('\n', i)
            i = len(text) if stop < 0 else stop
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1; break
                else:
                    i += 1
            out.append(' "" ')
        else:
            out.append(text[i]); i += 1
    if depth:
        raise ValueError('Unclosed block comment')
    return ''.join(out)

def run() -> dict:
    files = sorted((ROOT / 'lean' / 'BusyLean7').glob('*.lean'))
    hits = []
    counts = {'definitions': 0, 'theorems': 0, 'lines': 0}
    for path in files:
        raw = path.read_text()
        text = strip_comments_strings(raw)
        counts['definitions'] += len(re.findall(r'^\s*(?:private\s+)?def\s+', text, re.M))
        counts['theorems'] += len(re.findall(r'\btheorem\s+', text))
        counts['lines'] += raw.count('\n')
        for m in re.finditer(r'\b(sorry|admit|axiom|noncomputable|partial|unsafe|opaque|'
                             r'implemented_by|extern|native_decide)\b', text):
            hits.append({'path': str(path.relative_to(ROOT)), 'token': m.group()})
    defs = strip_comments_strings((ROOT / 'lean/BusyLean7/Definitions.lean').read_text())
    forbidden_dependencies = [x for x in ['BusyLean.contender_6', 'BusyLean.finalFamily',
                                          'BigNumber.contender_6'] if x in defs]
    vendors = json.loads((ROOT / 'evidence/vendor_hashes.json').read_text())
    for v in vendors:
        b = (ROOT / v['path']).read_bytes()
        v['actual_git_blob'] = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        v['identical'] = v['actual_git_blob'] == v['expected_git_blob']
    result = {'status': 'passed' if not hits and not forbidden_dependencies
              and all(v['identical'] for v in vendors) else 'failed',
              'scope': 'Lexical checks and exact vendor hashes; NOT Lean validation',
              'counts': counts, 'forbidden_token_hits': hits,
              'forbidden_direct_definition_references': forbidden_dependencies,
              'vendor_files': vendors, 'kernel_dependency_closure': 'not_run'}
    (ROOT/'evidence/source_audit.json').write_text(json.dumps(result, indent=2)+'\n')
    return result

if __name__ == '__main__':
    result = run()
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['status'] == 'passed' else 1)
