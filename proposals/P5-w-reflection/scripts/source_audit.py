#!/usr/bin/env python3
"""Syntactic source audit. This does NOT replace a kernel axiom audit."""
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]


def strip_comments(s: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1; i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif s.startswith('--', i):
            i = s.find('\n', i)
            if i < 0: break
        else:
            out.append(s[i]); i += 1
    if depth: raise ValueError('unclosed source comment')
    return ''.join(out)

report = {'scope': 'lexical inspection only; not Lean verification', 'files': []}
for p in sorted((ROOT/'lean').rglob('*.lean')):
    clean = strip_comments(p.read_text())
    bad = re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|noncomputable|opaque)\b', clean)
    row = {'file': str(p.relative_to(ROOT)), 'forbidden_declarations_or_placeholders': bad}
    report['files'].append(row)
    assert not bad, row
    if p.name == 'Definitions.lean':
        report['entry_definitions_reference_contender_5'] = bool(re.search(r'\bcontender_5\b', clean))
        assert not report['entry_definitions_reference_contender_5']
report['successful'] = True
(ROOT/'evidence/source_audit.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
