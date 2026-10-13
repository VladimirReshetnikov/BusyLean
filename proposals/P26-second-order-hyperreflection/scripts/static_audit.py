#!/usr/bin/env python3
"""Static hygiene audit for the Contender 20 overlay.

This is not a Lean kernel check. It rejects common nonconstructive or unfinished
source markers and verifies that the expected public declarations are present.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "repo_overlay"

FORBIDDEN_PATTERNS = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "axiom declaration": r"(?m)^\s*axiom\b",
    "noncomputable": r"\bnoncomputable\b",
    "unsafe": r"\bunsafe\b",
    "partial": r"\bpartial\b",
    "opaque": r"(?m)^\s*opaque\b",
    "extern": r"(?m)^\s*extern\b",
    "implemented_by": r"\bimplemented_by\b",
    "Classical.choice": r"\bClassical\.choice\b",
}

# Occurrences inside module comments are allowed only for the explicit
# constructivity statement in SecondOrderReflection.lean. Strip comments before
# checking executable source.
def strip_comments(text: str) -> str:
    # Remove nested Lean block comments conservatively.
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)

EXPECTED = {
    "BusyLean/SecondOrderReflection.lean": [
        "abbrev HyperLift",
        "def spliceLifts",
        "def stageHyperLift",
        "def liftLift",
        "def diagonalHyperLift",
    ],
    "BusyLean/SecondOrderReflectionFacts.lean": [
        "def GoodLift",
        "theorem diagonalHyperLift_preservesGoodLifts",
        "theorem diagonalHyperLift_strictlyLiftInflationary",
        "theorem diagonalHyperLift_rank_lt_succ",
    ],
    "BusyLean/Contender20.lean": [
        "def family19",
        "def schedule20",
        "def rank20",
        "def baseLift20",
        "def firstOrder20",
        "def F20",
        "def contender_20",
    ],
    "BusyLean/Comparison20.lean": [
        "theorem family19_lt_firstOrder20",
        "theorem firstOrder20_lt_F20",
        "theorem family19_lt_F20",
        "theorem contender_19_lt_contender_20",
    ],
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    failures: list[str] = []
    records: list[dict[str, object]] = []
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        rel = path.relative_to(LEAN_ROOT).as_posix()
        text = path.read_text(encoding="utf-8")
        code = strip_comments(text)
        hits: list[str] = []
        for label, pattern in FORBIDDEN_PATTERNS.items():
            if re.search(pattern, code):
                hits.append(label)
                failures.append(f"{rel}: forbidden marker {label}")
        missing = [needle for needle in EXPECTED.get(rel, []) if needle not in text]
        for needle in missing:
            failures.append(f"{rel}: missing declaration marker {needle!r}")
        records.append(
            {
                "file": rel,
                "lines": text.count("\n") + 1,
                "sha256": sha256(path),
                "forbidden_hits": hits,
                "missing_expected": missing,
            }
        )

    # Cross-file dependency checks.
    imports = {
        p.relative_to(LEAN_ROOT).as_posix(): re.findall(
            r"(?m)^import\s+([A-Za-z0-9_.]+)\s*$", p.read_text(encoding="utf-8")
        )
        for p in LEAN_ROOT.rglob("*.lean")
    }
    required_edges = {
        "BusyLean/SecondOrderReflectionFacts.lean": {
            "BusyLean.SecondOrderReflection",
            "BusyLean.HyperReflectionFacts",
        },
        "BusyLean/Contender20.lean": {
            "BusyLean.SecondOrderReflection",
            "BusyLean.Contender19",
        },
        "BusyLean/Comparison20.lean": {
            "BusyLean.Contender20",
            "BusyLean.SecondOrderReflectionFacts",
            "BusyLean.Comparison19",
        },
    }
    for rel, required in required_edges.items():
        missing = required.difference(imports.get(rel, []))
        for module in sorted(missing):
            failures.append(f"{rel}: missing import {module}")

    report = {
        "audit": "static source hygiene only; not a Lean kernel build",
        "status": "PASS" if not failures else "FAIL",
        "files": records,
        "failures": failures,
    }
    out = ROOT / "validation" / "static_audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(json.dumps(report, indent=2))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
