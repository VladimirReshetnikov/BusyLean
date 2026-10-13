#!/usr/bin/env python3
"""Lexical sanity checks only. This is NOT a Lean parser or a kernel checker."""
from __future__ import annotations
import ast
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def strip_comments_and_strings(source: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                i += 2
            elif source.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif source.startswith('/-', i):
            depth = 1
            i += 2
        elif source.startswith('--', i):
            j = source.find('\n', i)
            i = len(source) if j < 0 else j
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError('Unterminated double-quoted string')
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unterminated nested block comment')
    return ''.join(out)


def main() -> None:
    checks = []
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    banned = re.compile(r'\b(?:sorry|admit|axiom|native_decide|noncomputable|'
                        r'partial|unsafe|opaque|implemented_by|extern)\b')
    for path in sorted((ROOT / 'lean').rglob('*.lean')):
        text = strip_comments_and_strings(path.read_text(encoding='utf-8'))
        stack = []
        for char in text:
            if char in pairs.values():
                stack.append(char)
            elif char in pairs:
                if not stack or stack.pop() != pairs[char]:
                    raise ValueError(f'Unbalanced delimiter in {path}')
        if stack:
            raise ValueError(f'Unclosed delimiter in {path}: {stack}')
        matches = banned.findall(text)
        if matches:
            raise ValueError(f'Forbidden code token in {path}: {matches}')
        checks.append({'file': str(path.relative_to(ROOT)),
                       'delimiters': 'balanced', 'forbidden_tokens': []})
    python_files = list((ROOT / 'scripts').glob('*.py')) + list((ROOT / 'tests').glob('*.py'))
    for path in python_files:
        ast.parse(path.read_text(encoding='utf-8'), filename=str(path))
    record = {'status': 'passed', 'lean_files': checks,
              'python_syntax_files': len(python_files),
              'limitation': 'Lexical checks do not establish Lean compilation or theorem correctness.'}
    (ROOT / 'audit' / 'static-checks.json').write_text(
        json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(record, indent=2))

if __name__ == '__main__':
    main()
