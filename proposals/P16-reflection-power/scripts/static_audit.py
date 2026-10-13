#!/usr/bin/env python3
"""Conservative textual audit for the Contender 7 Lean overlay.

This is not a substitute for Lean's kernel.  It catches banned constructs,
accidental incumbent-value dependence, missing theorem declarations, malformed
ASCII delimiters, and drift from the intended definition.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CONTENDER = ROOT / "lean" / "BusyLean" / "Contender7.lean"
COMPARISON = ROOT / "lean" / "BusyLean" / "Comparison7.lean"
AUDIT = ROOT / "lean" / "test" / "Contender7Audit.lean"

FORBIDDEN = (
    "noncomputable",
    "partial ",
    "unsafe",
    "opaque ",
    "implemented_by",
    "extern ",
    "native_decide",
    "sorry",
    "admit",
    "axiom ",
)

REQUIRED_CONTENDER = (
    "abbrev StageOperator",
    "def liftStage",
    "def stageOrder",
    "def metaHeight",
    "def contender_7",
    "Nat.succ (42 + p5Family 0 42)",
    "stageOrder metaHeight p5Family index 42",
)

REQUIRED_PROOFS = (
    "def IndexDominates",
    "theorem seed_lt_stage_index",
    "theorem liftStage_child_lt",
    "theorem liftStage_indexDominates",
    "theorem stageOrder_indexDominates",
    "theorem stageOrder_step",
    "theorem stageOrder_zero_lt_succ",
    "theorem contender_6_lt_contender_7",
    "theorem contender_5_lt_contender_7",
    "theorem p5_lt_contender_7",
)


def strip_comments(text: str) -> str:
    # Good enough for this controlled source: remove block and line comments.
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--.*", "", text)
    return text


def balanced(text: str) -> bool:
    pairs = {')': '(', ']': '[', '}': '{'}
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
        elif ch in pairs:
            if not stack or stack.pop() != pairs[ch]:
                return False
    return not stack and not in_string


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    failures: list[str] = []
    texts = {p: p.read_text(encoding="utf-8") for p in (CONTENDER, COMPARISON, AUDIT)}
    production = strip_comments(texts[CONTENDER] + "\n" + texts[COMPARISON])

    for token in FORBIDDEN:
        if token in production:
            failures.append(f"forbidden token in production Lean: {token!r}")

    # The source may import the file Contender6, but the incumbent value itself
    # must not occur in the defining module.
    if re.search(r"\bcontender_6\b", strip_comments(texts[CONTENDER])):
        failures.append("Contender7.lean mentions the incumbent value contender_6")

    for needle in REQUIRED_CONTENDER:
        if needle not in texts[CONTENDER]:
            failures.append(f"missing contender fragment: {needle}")
    for needle in REQUIRED_PROOFS:
        if needle not in texts[COMPARISON]:
            failures.append(f"missing proof fragment: {needle}")

    for path, text in texts.items():
        if not balanced(strip_comments(text)):
            failures.append(f"unbalanced delimiters or string in {path.relative_to(ROOT)}")

    if "#assert_not_in_contender7_closure BusyLean.contender_7 :" not in texts[AUDIT]:
        failures.append("kernel audit does not ban dependency on incumbent value")

    report = {
        "status": "FAIL" if failures else "PASS",
        "files": {str(p.relative_to(ROOT)): sha256(p) for p in texts},
        "checks": {
            "forbidden_construct_scan": not any("forbidden token" in x for x in failures),
            "no_incumbent_value_dependency_in_definition": not any("incumbent value" in x for x in failures),
            "required_definition_fragments": not any("missing contender" in x for x in failures),
            "required_proof_fragments": not any("missing proof" in x for x in failures),
            "balanced_delimiters": not any("unbalanced" in x for x in failures),
            "kernel_closure_test_present": not any("kernel audit" in x for x in failures),
        },
        "failures": failures,
        "disclaimer": "Textual audit only; run lake build and the Lean audit file for kernel verification.",
    }
    out = ROOT / "logs" / "static_audit.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
