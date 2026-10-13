#!/usr/bin/env python3
"""Static preflight for the Contender 14 overlay.

This is deliberately not a substitute for `lake build` or the Lean kernel.
It catches integration mistakes before the overlay is copied into BusyLean:
forbidden declaration keywords, forbidden predecessor constants in the new
number's executable source, missing declarations, and accidental placeholders.
"""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEF = ROOT / "BusyLean" / "Contender14.lean"
PROOF = ROOT / "BusyLean" / "Comparison14.lean"


def strip_lean_comments_and_strings(text: str) -> str:
    """Remove nested /- -/ comments, -- comments, and string contents."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                i += 2
            elif text[i] == '"':
                in_string = False
                out.append('""')
                i += 1
            else:
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                break
            out.append("\n")
            i = j + 1
        elif text[i] == '"':
            in_string = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated Lean block comment")
    if in_string:
        raise ValueError("unterminated Lean string")
    return "".join(out)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    failures: list[str] = []
    for path in (DEF, PROOF):
        if not path.exists():
            failures.append(f"missing {path.relative_to(ROOT)}")

    if failures:
        print("\n".join(f"FAIL: {x}" for x in failures))
        return 1

    definition = strip_lean_comments_and_strings(DEF.read_text(encoding="utf-8"))
    proof = strip_lean_comments_and_strings(PROOF.read_text(encoding="utf-8"))
    combined = definition + "\n" + proof

    # Cheap delimiter sanity after comments and strings are removed.  This is
    # not a parser, but it catches many damaged-overlay and truncation errors.
    pairs = {")": "(", "]": "[", "}": "{"}
    stack: list[tuple[str, int]] = []
    for pos, ch in enumerate(combined):
        if ch in "([{":
            stack.append((ch, pos))
        elif ch in pairs:
            if not stack or stack[-1][0] != pairs[ch]:
                failures.append(f"unbalanced delimiter {ch!r} near offset {pos}")
                break
            stack.pop()
    else:
        if stack:
            failures.append(f"unclosed delimiter {stack[-1][0]!r} near offset {stack[-1][1]}")

    forbidden_tokens = [
        "noncomputable", "partial", "unsafe", "opaque", "implemented_by",
        "extern", "native_decide", "sorry", "admit", "axiom",
    ]
    for token in forbidden_tokens:
        if re.search(rf"\b{re.escape(token)}\b", combined):
            failures.append(f"forbidden token in executable Lean source: {token}")

    # The predecessor constant may occur in the proof module's theorem
    # statements, but never in the executable definition module.
    for name in [
        "contender_13", "contender_12", "contender_11", "contender_10",
        "contender_9", "contender_8", "contender_7", "contender_6",
        "contender_5",
    ]:
        if re.search(rf"\b{re.escape(name)}\b", definition):
            failures.append(f"definition module mentions forbidden constant {name}")

    expected_defs = [
        "reflectFdFamily", "fdFamilyTransformer", "tree14", "towerStep",
        "operatorTower", "family13", "iterateF13", "seed13", "F14",
        "contender_14",
    ]
    for name in expected_defs:
        if not re.search(rf"\bdef\s+{re.escape(name)}\b", definition):
            failures.append(f"missing definition {name}")

    expected_theorems = [
        "fdFamilyTransformer_progressive", "operatorTower_progressive",
        "operatorTower_level_lt_succ", "seed13_lt_F14",
        "fortyTwo_F13_steps_lt_F14", "contender_13_lt_contender_14",
        "fvalue_lt_contender_14",
    ]
    for name in expected_theorems:
        if not re.search(rf"\btheorem\s+{re.escape(name)}\b", proof):
            failures.append(f"missing theorem {name}")

    if "def contender_14 : Nat := F14 (F14 42)" not in DEF.read_text(encoding="utf-8"):
        failures.append("unexpected final-number definition")

    print(f"Contender14.lean sha256  {sha256(DEF)}")
    print(f"Comparison14.lean sha256 {sha256(PROOF)}")
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}")
        return 1
    print("PASS: static source audit")
    print("NOTE: this preflight is not a Lean kernel check")
    return 0


if __name__ == "__main__":
    sys.exit(main())
