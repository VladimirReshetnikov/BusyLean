#!/usr/bin/env python3
"""Static source checks for the proposed Contender 11 package.

This is intentionally not presented as a substitute for Lean's kernel.  It
catches packaging errors, forbidden declaration forms, accidental direct use
of old contender constants, unbalanced delimiters, and missing theorem names.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEF = ROOT / "lean" / "BusyLean" / "Contender11.lean"
PROOF = ROOT / "lean" / "BusyLean" / "Comparison11.lean"


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            newline = text.find("\n", i)
            if newline < 0:
                break
            out.append("\n")
            i = newline + 1
            continue
        out.append(text[i])
        i += 1
    if block_depth:
        raise ValueError("unterminated Lean block comment")
    return "".join(out)


def check_balanced(text: str) -> dict[str, int]:
    pairs = {")": "(", "]": "[", "}": "{"}
    counts = {"()": 0, "[]": 0, "{}": 0}
    stack: list[str] = []
    in_string = False
    escaped = False
    for ch in text:
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch in "([{":
            stack.append(ch)
        elif ch in ")]} ":
            if ch == " ":
                continue
            if not stack or stack.pop() != pairs[ch]:
                raise ValueError(f"unbalanced delimiter at {ch!r}")
            counts[{"(": "()", "[": "[]", "{": "{}"}[pairs[ch]]] += 1
    if stack or in_string:
        raise ValueError("unclosed delimiter or string")
    return counts


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    definition = DEF.read_text(encoding="utf-8")
    proof = PROOF.read_text(encoding="utf-8")
    executable_def = strip_lean_comments(definition)
    executable_proof = strip_lean_comments(proof)

    forbidden_definition = [
        "noncomputable",
        "partial",
        "unsafe",
        "opaque",
        "implemented_by",
        "extern",
        "native_decide",
        "sorry",
        "admit",
        "axiom",
    ]
    forbidden_proof = [
        "sorry",
        "admit",
        "axiom",
        "native_decide",
        "Classical.choice",
    ]
    old_constants = [f"contender_{i}" for i in range(5, 11)]

    findings: list[str] = []
    for token in forbidden_definition:
        if re.search(rf"\b{re.escape(token)}\b", executable_def):
            findings.append(f"definition source contains forbidden token {token}")
    for token in forbidden_proof:
        if re.search(rf"\b{re.escape(token)}\b", executable_proof):
            findings.append(f"proof source contains forbidden token {token}")
    for token in old_constants:
        if re.search(rf"\b{re.escape(token)}\b", executable_def):
            findings.append(f"definition source directly references {token}")

    required_definitions = [
        "abbrev Operator",
        "def reflect",
        "def lift",
        "def autonomous",
        "def ramified",
        "def family10",
        "def F11",
        "def contender_11",
    ]
    required_theorems = [
        "theorem reflect_dominates",
        "theorem op_lt_autonomous",
        "theorem ramified_dominates",
        "theorem ramified_level_lt",
        "theorem ramified_lt_of_lt",
        "theorem family10_lt_F11",
        "theorem fixed_rank_eventually_lt_F11",
        "theorem fvalue_lt_F11",
        "theorem contender_10_lt_contender_11",
    ]
    for item in required_definitions:
        if item not in executable_def:
            findings.append(f"missing required definition marker: {item}")
    for item in required_theorems:
        if item not in executable_proof:
            findings.append(f"missing required theorem marker: {item}")

    if "def contender_11 : Nat := F11 (F11 42)" not in executable_def:
        findings.append("final diagonal definition is not in the expected form")
    if "RK.ramified (family10 n + 1)" not in executable_def:
        findings.append("F11 does not use the proposed input-dependent rank")
    if "import BusyLean.Contender10" not in executable_def:
        findings.append("definition module does not import Contender10")

    delimiter_counts = {
        "Contender11.lean": check_balanced(executable_def),
        "Comparison11.lean": check_balanced(executable_proof),
    }

    report = {
        "status": "PASS" if not findings else "FAIL",
        "scope": "static source and packaging checks; not a Lean kernel check",
        "files": {
            str(DEF.relative_to(ROOT)): {
                "sha256": sha256(DEF),
                "lines": len(definition.splitlines()),
                "max_line_length": max(map(len, definition.splitlines())),
            },
            str(PROOF.relative_to(ROOT)): {
                "sha256": sha256(PROOF),
                "lines": len(proof.splitlines()),
                "max_line_length": max(map(len, proof.splitlines())),
            },
        },
        "delimiter_counts": delimiter_counts,
        "forbidden_definition_tokens_checked": forbidden_definition,
        "forbidden_proof_tokens_checked": forbidden_proof,
        "old_contender_constants_checked_in_definition": old_constants,
        "findings": findings,
    }
    output = ROOT / "validation" / "static_audit.json"
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    raise SystemExit(0 if not findings else 1)


if __name__ == "__main__":
    main()
