#!/usr/bin/env python3
"""Static validation for the Contender 14 overlay.

This is deliberately not a substitute for Lean kernel checking.  It catches
forbidden constructs, accidental references to earlier contender constants,
missing declarations, malformed file layout, and inconsistent baseline data.
"""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEF = ROOT / "repo_overlay" / "BusyLean" / "Contender14.lean"
PROOF = ROOT / "repo_overlay" / "BusyLean" / "Comparison14.lean"

FORBIDDEN_TOKENS = [
    "noncomputable", "partial", "unsafe", "opaque", "implemented_by",
    "extern", "native_decide", "sorry", "admit", "axiom ",
]
FORBIDDEN_CONSTANTS = [f"contender_{i}" for i in range(5, 14)]
REQUIRED_DEF_NAMES = [
    "reflect14", "fdFamilyTransformer", "schedule14",
    "diagonalOperatorTower", "family13", "tower14", "F14", "contender_14",
]
REQUIRED_THEOREMS = [
    "lt_reflect14", "oracle_lt_reflect14", "fvalue_lt_reflect14",
    "fdFamilyTransformer_progressive", "diagonalOperatorTower_progressive",
    "transformer_lt_operatorStage_schedule14",
    "diagonalOperatorTower_step_lt", "diagonalOperatorTower_rank_lt",
    "family13_lt_F14", "input_lt_F14", "lower_rank_lt_F14",
    "reflect14_seed_lt_F14", "fvalue_lt_F14", "tower14_rank_at_42",
    "contender_13_lt_contender_14",
]


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    raise SystemExit(1)


def main() -> None:
    for path in (DEF, PROOF):
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        raw = path.read_bytes()
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            fail(f"non-UTF-8 source in {path}: {exc}")
        if b"\r\n" in raw:
            fail(f"CRLF line endings in {path}")
        # Strip block and line comments for token checks.
        code = re.sub(r"/-.*?-/", "", text, flags=re.S)
        code = re.sub(r"--.*", "", code)
        for token in FORBIDDEN_TOKENS:
            if token in code:
                fail(f"forbidden token {token!r} in {path.name}")

    defs = DEF.read_text(encoding="utf-8")
    proofs = PROOF.read_text(encoding="utf-8")

    for name in REQUIRED_DEF_NAMES:
        if not re.search(rf"\bdef\s+{re.escape(name)}\b", defs):
            fail(f"missing definition {name}")
    for name in REQUIRED_THEOREMS:
        if not re.search(rf"\btheorem\s+{re.escape(name)}\b", proofs):
            fail(f"missing theorem {name}")

    # The definition file may discuss the old constant in comments, but the
    # executable source must not mention it or any earlier contender constant.
    code_defs = re.sub(r"/-.*?-/", "", defs, flags=re.S)
    code_defs = re.sub(r"--.*", "", code_defs)
    for name in FORBIDDEN_CONSTANTS:
        if re.search(rf"\b{re.escape(name)}\b", code_defs):
            fail(f"definition depends textually on forbidden constant {name}")

    if "def contender_14 : Nat := F14 (F14 42)" not in defs:
        fail("unexpected final contender definition")
    if "def family13 (n : Nat) : Nat := F13 (F13 n)" not in defs:
        fail("family13 is not the expected construction-level predecessor")
    if "(family13 n)" not in defs.split("def tower14", 1)[1]:
        fail("tower height is not self-indexed by family13")

    for path in (DEF, PROOF):
        text = path.read_text(encoding="utf-8")
        if text.count("namespace BusyLean") != 1 or text.count("end BusyLean") != 1:
            fail(f"unexpected namespace framing in {path.name}")
        for left, right in (("(", ")"), ("[", "]"), ("{", "}")):
            if text.count(left) != text.count(right):
                fail(f"unbalanced {left}{right} delimiters in {path.name}")
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        print(f"OK   {path.relative_to(ROOT)}  sha256={digest}")
    print("PASS: static overlay checks completed")
    print("NOTE: Lean 4.34.0 kernel checking remains mandatory after applying the overlay.")


if __name__ == "__main__":
    main()
