#!/usr/bin/env python3
"""Conservative source-level audit for the Contender 14 overlay.

This is not a Lean kernel check.  It catches prohibited implementation tokens,
accidental references to earlier contender constants in the new definition
modules, delimiter imbalance, trailing whitespace, tabs, and overlong lines.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "overlay" / "BusyLean"
DEFINITION_FILES = [LEAN / "HyperReflection.lean", LEAN / "Contender14.lean"]
ALL_LEAN = sorted((ROOT / "overlay").rglob("*.lean"))

PROHIBITED = {
    "noncomputable",
    "partial",
    "unsafe",
    "opaque",
    "implemented_by",
    "extern",
    "sorry",
    "admit",
    "Classical.choice",
    "native_decide",
}
FORBIDDEN_CONSTANTS = {f"contender_{i}" for i in range(5, 14)}


def strip_comments_and_strings(text: str) -> str:
    """Remove Lean strings, line comments, and nested block comments."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                i += 2
            elif text[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
            continue
        if text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    if depth or in_string:
        raise ValueError(f"unterminated lexical construct: block_depth={depth}, string={in_string}")
    return "".join(out)


def balanced(text: str) -> tuple[bool, str]:
    pairs = {")": "(", "]": "[", "}": "{"}
    stack: list[tuple[str, int]] = []
    for pos, ch in enumerate(text):
        if ch in "([{":
            stack.append((ch, pos))
        elif ch in pairs:
            if not stack or stack[-1][0] != pairs[ch]:
                return False, f"unexpected {ch!r} at byte {pos}"
            stack.pop()
    if stack:
        return False, f"unclosed {stack[-1][0]!r} at byte {stack[-1][1]}"
    return True, "ok"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def main() -> int:
    failures: list[str] = []
    records: list[dict[str, object]] = []

    for path in ALL_LEAN:
        text = path.read_text(encoding="utf-8")
        try:
            code = strip_comments_and_strings(text)
        except ValueError as exc:
            failures.append(f"{path.relative_to(ROOT)}: {exc}")
            code = text

        ok, note = balanced(code)
        if not ok:
            failures.append(f"{path.relative_to(ROOT)}: delimiter check: {note}")

        bad_tokens = sorted(
            token for token in PROHIBITED
            if re.search(rf"(?<![A-Za-z0-9_]){re.escape(token)}(?![A-Za-z0-9_])", code)
        )
        if bad_tokens:
            failures.append(f"{path.relative_to(ROOT)}: prohibited tokens {bad_tokens}")

        lines = text.splitlines()
        tabs = [i + 1 for i, line in enumerate(lines) if "\t" in line]
        trailing = [i + 1 for i, line in enumerate(lines) if line.rstrip() != line]
        long = [i + 1 for i, line in enumerate(lines) if len(line) > 100]
        if tabs:
            failures.append(f"{path.relative_to(ROOT)}: tabs on lines {tabs}")
        if trailing:
            failures.append(f"{path.relative_to(ROOT)}: trailing whitespace on lines {trailing}")
        if long:
            failures.append(f"{path.relative_to(ROOT)}: lines over 100 columns {long}")

        records.append({
            "path": str(path.relative_to(ROOT)),
            "sha256": sha256(path),
            "lines": len(lines),
            "delimiter_check": note,
            "prohibited_tokens": bad_tokens,
            "tabs": tabs,
            "trailing_whitespace": trailing,
            "over_100_columns": long,
        })

    for path in DEFINITION_FILES:
        code = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        hits = sorted(name for name in FORBIDDEN_CONSTANTS if re.search(rf"\b{name}\b", code))
        if hits:
            failures.append(
                f"{path.relative_to(ROOT)}: forbidden earlier contender constants {hits}"
            )

    result = {
        "kind": "source-level audit only; not a Lean kernel check",
        "root": str(ROOT),
        "files": records,
        "definition_files_for_constant_check": [str(p.relative_to(ROOT)) for p in DEFINITION_FILES],
        "prohibited_tokens": sorted(PROHIBITED),
        "forbidden_constant_names": sorted(FORBIDDEN_CONSTANTS),
        "status": "PASS" if not failures else "FAIL",
        "failures": failures,
    }
    out = ROOT / "artifacts" / "static_audit.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    report = [
        "STATIC SOURCE AUDIT",
        "===================",
        "",
        "This audit is intentionally weaker than Lean kernel replay.",
        "It checks source hygiene and dependency-name constraints only.",
        "",
        f"Status: {result['status']}",
        f"Lean files checked: {len(records)}",
        f"Definition files checked for earlier contender constants: {len(DEFINITION_FILES)}",
    ]
    if failures:
        report += ["", "Failures:"] + [f"- {failure}" for failure in failures]
    else:
        report += [
            "",
            "No prohibited implementation token was found outside comments/strings.",
            "No earlier contender constant occurs in the new definition modules.",
            "All checked delimiters are balanced.",
            "No tabs, trailing whitespace, or lines over 100 columns were found.",
        ]
    (ROOT / "artifacts" / "static_audit.txt").write_text(
        "\n".join(report) + "\n", encoding="utf-8"
    )
    print("\n".join(report))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
