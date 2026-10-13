#!/usr/bin/env python3
"""Static, non-kernel audit for the Contender 20 proposal.

This script deliberately does not pretend to replace Lean elaboration.  It
checks source hygiene, expected declaration presence, the no-laziness source
condition, line lengths, UTF-8 validity, and file hashes.  Kernel replay is the
job of overlay/scripts/check20.py in a Lean 4.34.0 checkout.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
LIB = PACKAGE / "overlay" / "BusyLean"
REPORT = PACKAGE / "artifacts" / "static_audit_report.json"

LIBRARY_FILES = [
    LIB / "SuperReflection.lean",
    LIB / "SuperReflectionFacts.lean",
    LIB / "Contender20.lean",
    LIB / "Comparison20.lean",
]

FORBIDDEN_WORDS = {
    "admit",
    "axiom",
    "implemented_by",
    "native_decide",
    "noncomputable",
    "opaque",
    "partial",
    "sorry",
    "unsafe",
    "extern",
}
FORBIDDEN_COMMANDS = {
    "#eval",
    "#reduce",
    "run_cmd",
    "initialize",
    "elab",
    "macro",
}

EXPECTED = {
    "SuperReflection.lean": [
        "abbrev LiftTransformer",
        "def spliceLifts",
        "def promoteLift",
        "def liftStage",
        "def superClosure",
        "def superIterate",
    ],
    "SuperReflectionFacts.lean": [
        "def GoodLift",
        "theorem spliceLifts_good",
        "theorem promoteLift_good",
        "theorem baseLift_lt_liftStage",
        "theorem superIterate_good",
        "theorem lift_lt_superIterate_succ",
    ],
    "Contender20.lean": [
        "def family19",
        "def schedule20",
        "def lift20",
        "def hyperFamily20",
        "def F20",
        "def contender_20",
    ],
    "Comparison20.lean": [
        "theorem diagonalLift_lt_lift20",
        "theorem family19_lt_F20",
        "theorem final_lvalue_lt_F20",
        "theorem contender_19_lt_contender_20",
    ],
}


def strip_lean(text: str) -> str:
    """Remove nested block comments, line comments, chars, and strings."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    in_char = False
    escape = False
    while i < n:
        pair = text[i : i + 2]
        ch = text[i]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                i += 2
            elif pair == "-/":
                block_depth -= 1
                i += 2
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
            continue
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            if ch == "\n":
                out.append("\n")
            i += 1
            continue
        if in_char:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == "'":
                in_char = False
            i += 1
            continue
        if pair == "/-":
            block_depth = 1
            i += 2
        elif pair == "--":
            newline = text.find("\n", i + 2)
            if newline == -1:
                break
            out.append("\n")
            i = newline + 1
        elif ch == '"':
            in_string = True
            i += 1
        elif ch == "'":
            # Lean identifiers can contain apostrophes. Treat an apostrophe as
            # a char delimiter only when followed by exactly one codepoint and
            # another apostrophe; this is enough for this package's sources.
            if i + 2 < n and text[i + 2] == "'":
                in_char = True
            else:
                out.append(ch)
            i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    failures: list[str] = []
    results: dict[str, object] = {
        "audit_kind": "static_source_audit_not_kernel_replay",
        "package": PACKAGE.name,
        "files": {},
        "checks": {},
    }

    for path in LIBRARY_FILES:
        if not path.is_file():
            failures.append(f"missing library source: {path}")
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as exc:
            failures.append(f"invalid UTF-8 in {path.name}: {exc}")
            continue
        code = strip_lean(text)
        words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", code))
        forbidden_words = sorted(words & FORBIDDEN_WORDS)
        forbidden_commands = sorted(cmd for cmd in FORBIDDEN_COMMANDS if cmd in code)
        missing = [decl for decl in EXPECTED[path.name] if decl not in code]
        long_lines = [
            {"line": no, "length": len(line)}
            for no, line in enumerate(text.splitlines(), start=1)
            if len(line) > 100
        ]
        if forbidden_words:
            failures.append(f"{path.name}: forbidden words {forbidden_words}")
        if forbidden_commands:
            failures.append(f"{path.name}: forbidden commands {forbidden_commands}")
        if missing:
            failures.append(f"{path.name}: missing declarations {missing}")
        if long_lines:
            failures.append(f"{path.name}: lines over 100 columns {long_lines}")
        results["files"][path.name] = {
            "sha256": sha256(path),
            "bytes": path.stat().st_size,
            "lines": len(text.splitlines()),
            "forbidden_words": forbidden_words,
            "forbidden_commands": forbidden_commands,
            "missing_expected_declarations": missing,
            "lines_over_100_columns": long_lines,
        }

    contender = strip_lean((LIB / "Contender20.lean").read_text(encoding="utf-8"))
    no_lazy_constant = re.search(r"\bcontender_19\b", contender) is None
    uses_previous_construction = re.search(r"\bF19\b", contender) is not None
    closed_nat = re.search(r"def\s+contender_20\s*:\s*Nat\s*:=", contender) is not None
    has_structural_nat_recursion = "def superIterate" in strip_lean(
        (LIB / "SuperReflection.lean").read_text(encoding="utf-8")
    )
    results["checks"] = {
        "definition_source_avoids_previous_contender_constant": no_lazy_constant,
        "definition_source_uses_previous_construction_F19": uses_previous_construction,
        "contender_20_is_declared_closed_Nat": closed_nat,
        "meta_rank_is_structural_Nat_recursion": has_structural_nat_recursion,
        "kernel_replay_performed": False,
    }
    if not no_lazy_constant:
        failures.append("Contender20.lean mentions the previous contender constant")
    if not uses_previous_construction:
        failures.append("Contender20.lean does not use F19 as the documented seed")
    if not closed_nat:
        failures.append("contender_20 is not visibly declared as a Nat definition")

    results["status"] = "PASS" if not failures else "FAIL"
    results["failures"] = failures
    REPORT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2, sort_keys=True))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
