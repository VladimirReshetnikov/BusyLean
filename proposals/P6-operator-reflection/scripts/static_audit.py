#!/usr/bin/env python3
"""Static rule audit for the Contender 7 overlay.

This does not replace Lean kernel checking.  It checks the syntactic contest
exclusions, expected theorem/definition names, import layering, and the absence
of a dependency on `BusyLean.contender_6` in definition modules.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "repo_overlay" / "BusyLean"
TEST = ROOT / "repo_overlay" / "test"

FORBIDDEN = [
    r"\bnoncomputable\b",
    r"\bpartial\b",
    r"\bunsafe\b",
    r"\bopaque\b",
    r"\bimplemented_by\b",
    r"\bextern\b",
    r"\bnative_decide\b",
    r"\bsorry\b",
    r"\badmit\b",
    r"\baxiom\b",
]
REQUIRED = {
    "MetaReflection.lean": [
        "abbrev Transformer",
        "def reflectionTransformer",
        "def runTransformer",
        "def liftTransformer",
        "def operatorStage",
    ],
    "MetaReflectionFacts.lean": [
        "def Progressive",
        "theorem reflectionTransformer_progressive",
        "theorem transformer_lt_lift_at",
        "theorem operatorStage_progressive",
        "theorem operatorStage_child_lt",
    ],
    "Contender7.lean": [
        "def autonomousTransformer",
        "def autonomousFamily",
        "def contender_7",
    ],
    "Comparison7.lean": [
        "theorem contender_6_lt_contender_7",
        "theorem contender_5_lt_contender_7",
        "theorem defined_operator_eventually_lt",
    ],
}
TEST_REQUIRED = {
    "Contender7Audit.lean": [
        "#print axioms BusyLean.contender_7",
        "#assert_contender7_not_in_closure BusyLean.contender_7",
        "BusyLean.contender_6 BusyLean.finalFamily BusyLean.contender_5",
    ],
    "MetaReflectionSmoke.lean": [
        "#eval runTransformer plusOneTransformer",
        "example : runTransformer plusOneTransformer",
    ],
}


def strip_comments(text: str) -> str:
    # Sufficient for this controlled source: remove line comments and nested-free
    # block comments before token checks.
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--.*", "", text)


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    raise SystemExit(1)


def main() -> None:
    files = sorted(LEAN.glob("*.lean")) + sorted(TEST.glob("*.lean"))
    if not files:
        fail("no Lean files found")

    for path in files:
        raw = path.read_text(encoding="utf-8")
        code = strip_comments(raw)
        for pattern in FORBIDDEN:
            if re.search(pattern, code):
                fail(f"{path.relative_to(ROOT)} contains forbidden pattern {pattern!r}")

    for name, needles in REQUIRED.items():
        text = (LEAN / name).read_text(encoding="utf-8")
        for needle in needles:
            if needle not in text:
                fail(f"{name} is missing {needle!r}")

    for name, needles in TEST_REQUIRED.items():
        text = (TEST / name).read_text(encoding="utf-8")
        for needle in needles:
            if needle not in text:
                fail(f"{name} is missing {needle!r}")

    definition_text = "\n".join(
        (LEAN / name).read_text(encoding="utf-8")
        for name in ["MetaReflection.lean", "Contender7.lean"]
    )
    code = strip_comments(definition_text)
    if re.search(r"\bcontender_6\b", code):
        fail("definition layer mentions the previous contender constant")

    audit_code = strip_comments(
        (TEST / "Contender7Audit.lean").read_text(encoding="utf-8")
    )
    if "#eval BusyLean.contender_7" in audit_code:
        fail("audit attempts to evaluate contender_7")

    expected_imports = {
        "MetaReflection.lean": ["import BusyLean.Contender6"],
        "Contender7.lean": ["import BusyLean.MetaReflection"],
        "MetaReflectionFacts.lean": [
            "import BusyLean.MetaReflection",
            "import BusyLean.ReflectionFacts",
        ],
        "Comparison7.lean": [
            "import BusyLean.Contender7",
            "import BusyLean.MetaReflectionFacts",
            "import BusyLean.Comparison",
        ],
    }
    for name, needles in expected_imports.items():
        text = (LEAN / name).read_text(encoding="utf-8")
        for needle in needles:
            if needle not in text:
                fail(f"{name} is missing required layering import {needle!r}")

    comparison = (LEAN / "Comparison7.lean").read_text(encoding="utf-8")
    if "Nat.lt_trans contender_5_lt_contender_6 contender_6_lt_contender_7" not in comparison:
        fail("expected transitive comparison chain is absent")

    imports = (ROOT / "repo_overlay" / "BusyLean.lean").read_text(encoding="utf-8")
    for module in ["MetaReflection", "MetaReflectionFacts", "Contender7", "Comparison7"]:
        if f"import BusyLean.{module}" not in imports:
            fail(f"BusyLean.lean does not import {module}")

    print(f"PASS: audited {len(files)} Lean files")
    print("PASS: no forbidden constructive-rule tokens in code")
    print("PASS: definition layer does not mention contender_6")
    print("PASS: expected definitions, theorems, tests, and imports are present")
    print("PASS: audit contains transitive closure rejection and no contender evaluation")


if __name__ == "__main__":
    main()
