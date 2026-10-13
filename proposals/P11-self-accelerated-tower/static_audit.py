#!/usr/bin/env python3
"""Conservative source-level audit for the Contender 11 package.

This is not a replacement for Lean's kernel, `#print axioms`, or the repository's
transitive dependency audit. It catches accidental use of constructs forbidden
by the BusyLean rules and accidental direct mention of earlier contender
constants in the definition module.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DEFINITION = ROOT / "lean" / "BusyLean" / "Contender11.lean"
PROOF = ROOT / "lean" / "BusyLean" / "Comparison11.lean"

FORBIDDEN_ANYWHERE = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "axiom": r"\baxiom\b",
    "noncomputable": r"\bnoncomputable\b",
    "partial": r"\bpartial\b",
    "unsafe": r"\bunsafe\b",
    "opaque": r"\bopaque\b",
    "implemented_by": r"\bimplemented_by\b",
    "extern": r"\bextern\b",
    "native_decide": r"\bnative_decide\b",
    "Classical.choice": r"\bClassical\.choice\b",
}

FORBIDDEN_IN_DEFINITION = [
    "contender_10",
    "contender_9",
    "contender_8",
    "contender_7",
    "contender_6",
    "contender_5",
]


def strip_comments_and_strings(text: str) -> str:
    """Remove nested Lean block comments, line comments, and string contents."""
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
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            newline = text.find("\n", i)
            i = len(text) if newline < 0 else newline
        elif text[i] == '"':
            in_string = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated block comment")
    if in_string:
        raise ValueError("unterminated string")
    return "".join(out)


def main() -> int:
    failures: list[str] = []
    for path in (DEFINITION, PROOF):
        raw = path.read_text(encoding="utf-8")
        try:
            code = strip_comments_and_strings(raw)
        except ValueError as exc:
            failures.append(f"{path.relative_to(ROOT)}: {exc}")
            continue
        for label, pattern in FORBIDDEN_ANYWHERE.items():
            if re.search(pattern, code):
                failures.append(
                    f"{path.relative_to(ROOT)}: forbidden construct {label!r}"
                )
        long_lines = [
            number
            for number, line in enumerate(raw.splitlines(), 1)
            if len(line) > 100
        ]
        if long_lines:
            failures.append(
                f"{path.relative_to(ROOT)}: lines longer than 100 columns: "
                + ", ".join(map(str, long_lines))
            )

    definition_code = strip_comments_and_strings(
        DEFINITION.read_text(encoding="utf-8")
    )
    for name in FORBIDDEN_IN_DEFINITION:
        if re.search(rf"\b{re.escape(name)}\b", definition_code):
            failures.append(
                f"{DEFINITION.relative_to(ROOT)} directly mentions {name}"
            )

    required = {
        "reflect11",
        "stage11",
        "round11",
        "family10",
        "tower11",
        "F11",
        "contender_11",
        "contender_10_lt_contender_11",
    }
    combined = DEFINITION.read_text(encoding="utf-8") + PROOF.read_text(
        encoding="utf-8"
    )
    missing = sorted(name for name in required if name not in combined)
    if missing:
        failures.append("missing required declarations: " + ", ".join(missing))

    if failures:
        print("STATIC AUDIT: FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print("STATIC AUDIT: PASS")
    print("- no forbidden Lean constructs found outside comments/strings")
    print("- definition module does not mention earlier contender constants")
    print("- all source lines are at most 100 columns")
    print("- required declarations are present")
    print("NOTE: this is not a Lean kernel check; run the bundled Lean audit.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
