#!/usr/bin/env python3
"""Fast source-level audit; this does not replace Lean kernel checking."""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFINITION = ROOT / "BusyLean" / "Contender14.lean"
PROOF = ROOT / "BusyLean" / "Comparison14.lean"

FORBIDDEN_CONSTRUCTS = [
    r"\bnoncomputable\b",
    r"\bpartial\b",
    r"\bunsafe\b",
    r"\bopaque\b",
    r"\bimplemented_by\b",
    r"\bextern\b",
    r"\bnative_decide\b",
    r"\bClassical\.choice\b",
    r"\bsorry\b",
    r"\baxiom\b",
]
FORBIDDEN_CONSTANTS = [rf"\bcontender_{n}\b" for n in range(5, 14)]
REQUIRED_DEFINITIONS = [
    "reflect14",
    "fdTransformer",
    "tree14",
    "operatorPower",
    "family13",
    "F14",
    "contender_14",
]
REQUIRED_THEOREMS = [
    "operatorPower_progressive",
    "operatorPower_step_lt",
    "family13_twice_lt_F14",
    "family13_lt_F14",
    "fvalue_lt_F14",
    "contender_13_lt_contender_14",
]


def strip_comments(text: str) -> str:
    # Good enough for this source audit: remove nested-looking block comments
    # iteratively, then line comments. Lean itself remains the authority.
    old = None
    while old != text:
        old = text
        text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--.*", "", text)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def main() -> int:
    definition_raw = DEFINITION.read_text(encoding="utf-8")
    proof_raw = PROOF.read_text(encoding="utf-8")
    definition = strip_comments(definition_raw)
    combined = strip_comments(definition_raw + "\n" + proof_raw)

    errors: list[str] = []
    for pattern in FORBIDDEN_CONSTRUCTS:
        if re.search(pattern, combined):
            errors.append(f"forbidden construct matched: {pattern}")
    for pattern in FORBIDDEN_CONSTANTS:
        if re.search(pattern, definition):
            errors.append(f"definition mentions earlier contender constant: {pattern}")
    for name in REQUIRED_DEFINITIONS:
        if not re.search(rf"\bdef\s+{re.escape(name)}\b", definition):
            errors.append(f"missing definition: {name}")
    for name in REQUIRED_THEOREMS:
        if not re.search(rf"\btheorem\s+{re.escape(name)}\b", combined):
            errors.append(f"missing theorem: {name}")

    for path in (DEFINITION, PROOF):
        long_lines = [
            i for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1)
            if len(line) > 100
        ]
        if long_lines:
            errors.append(f"{path.name}: lines over 100 columns: {long_lines}")

    if errors:
        print("STATIC AUDIT FAILED")
        for error in errors:
            print(f"- {error}")
        return 1

    print("STATIC AUDIT PASSED")
    print(f"Contender14.lean  sha256={sha256(DEFINITION)}")
    print(f"Comparison14.lean sha256={sha256(PROOF)}")
    print("No forbidden construct or earlier contender constant occurs in the")
    print("comment-stripped definition source. Kernel checking is still required.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
