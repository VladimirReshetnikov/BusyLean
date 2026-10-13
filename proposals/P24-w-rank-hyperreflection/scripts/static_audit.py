#!/usr/bin/env python3
"""Static, compiler-independent sanity checks for the Contender-20 overlay."""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_FILES = [
    ROOT / "BusyLean" / "TransfiniteHyperReflection.lean",
    ROOT / "BusyLean" / "Contender20.lean",
    ROOT / "BusyLean" / "Comparison20.lean",
]
FORBIDDEN = {
    "axiom",
    "noncomputable",
    "partial",
    "unsafe",
    "extern",
    "implemented_by",
    "sorry",
    "admit",
}


def strip_comments(text: str) -> str:
    """Remove nested Lean block comments and line comments conservatively."""
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
            if j < 0:
                break
            out.append("\n")
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def balanced(text: str) -> bool:
    pairs = {")": "(", "]": "[", "}": "{"}
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


def main() -> int:
    report: dict[str, object] = {"files": {}, "status": "PASS"}
    for path in LEAN_FILES:
        raw = path.read_text(encoding="utf-8")
        code = strip_comments(raw)
        words = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", code))
        bad = sorted(FORBIDDEN & words)
        item = {
            "bytes": len(raw.encode("utf-8")),
            "lines": raw.count("\n") + 1,
            "sha256": hashlib.sha256(raw.encode("utf-8")).hexdigest(),
            "forbidden_tokens": bad,
            "balanced_delimiters": balanced(code),
            "max_line_length": max(map(len, raw.splitlines()), default=0),
        }
        report["files"][str(path.relative_to(ROOT))] = item
        if bad or not item["balanced_delimiters"]:
            report["status"] = "FAIL"
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
