#!/usr/bin/env python3
"""Static, non-kernel audit for the Contender 11 source package."""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEF = ROOT / "candidate" / "BusyLean" / "Contender11.lean"
PROOF = ROOT / "candidate" / "BusyLean" / "Comparison11.lean"
AUDIT = ROOT / "candidate" / "test" / "Audit11.lean"
SMOKE = ROOT / "candidate" / "test" / "Contender11Smoke.lean"

FORBIDDEN = {
    "noncomputable", "partial", "unsafe", "opaque", "implemented_by",
    "extern", "native_decide", "sorry", "admit", "axiom",
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def strip_lean_comments_and_strings(text: str) -> str:
    """Replace comments/strings by spaces while preserving newlines.

    Lean block comments nest, so a regular expression is insufficient.
    """
    out: list[str] = []
    i = 0
    block_depth = 0
    line_comment = False
    in_string = False
    escape = False
    while i < len(text):
        c = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if line_comment:
            if c == "\n":
                line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if c == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif c == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if in_string:
            if c == "\n":
                # Lean strings normally do not contain raw newlines, but keep
                # line accounting stable if one appears.
                out.append("\n")
            else:
                out.append(" ")
            if escape:
                escape = False
            elif c == "\\":
                escape = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if c == "-" and nxt == "-":
            line_comment = True
            out.extend((" ", " "))
            i += 2
        elif c == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    if block_depth or in_string:
        raise ValueError("unterminated Lean block comment or string")
    return "".join(out)


def tokens(text: str) -> set[str]:
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", text))


def balanced(text: str) -> tuple[bool, str]:
    pairs = {")": "(", "]": "[", "}": "{"}
    stack: list[tuple[str, int]] = []
    for pos, c in enumerate(text):
        if c in "([{":
            stack.append((c, pos))
        elif c in pairs:
            if not stack or stack[-1][0] != pairs[c]:
                return False, f"unmatched {c!r} at byte {pos}"
            stack.pop()
    if stack:
        return False, f"unclosed {stack[-1][0]!r} at byte {stack[-1][1]}"
    return True, "balanced"


def audit() -> dict[str, object]:
    files = [DEF, PROOF, AUDIT, SMOKE]
    checks: list[dict[str, object]] = []
    failures: list[str] = []
    file_info: dict[str, object] = {}

    clean: dict[Path, str] = {}
    for path in files:
        raw = path.read_text(encoding="utf-8")
        stripped = strip_lean_comments_and_strings(raw)
        clean[path] = stripped
        found = sorted(FORBIDDEN & tokens(stripped))
        ok_balanced, balance_note = balanced(stripped)
        rel = str(path.relative_to(ROOT))
        file_info[rel] = {
            "bytes": path.stat().st_size,
            "lines": raw.count("\n") + 1,
            "sha256": sha256(path),
            "forbidden_tokens": found,
            "delimiter_check": balance_note,
        }
        if found:
            failures.append(f"{rel}: forbidden tokens {found}")
        if not ok_balanced:
            failures.append(f"{rel}: {balance_note}")

    def record(name: str, condition: bool, detail: str) -> None:
        checks.append({"name": name, "passed": condition, "detail": detail})
        if not condition:
            failures.append(f"{name}: {detail}")

    def_src = clean[DEF]
    proof_src = clean[PROOF]
    record(
        "definition avoids named previous scalar",
        "contender_10" not in tokens(def_src),
        "comments may discuss contender_10; executable syntax must not reference it",
    )
    record(
        "definition imports only prior definition phase",
        "import BusyLean.Contender10" in DEF.read_text(encoding="utf-8")
        and "Comparison10" not in def_src,
        "keeps proof modules out of the definition dependency closure",
    )
    for name in ["reflect11", "stage11", "crown11", "family10", "F11", "contender_11"]:
        record(f"definition {name} present", bool(re.search(rf"\bdef\s+{name}\b", def_src)), name)
    for name in [
        "oracle_lt_reflect11", "fvalue_lt_reflect11", "stage11_crown_step_lt",
        "family10_lt_F11", "defined_tree_eventually_lt11",
        "root_program_lt_F11", "contender_10_lt_contender_11",
    ]:
        record(f"theorem {name} present", bool(re.search(rf"\btheorem\s+{name}\b", proof_src)), name)
    record(
        "required comparison has strict target",
        bool(re.search(
            r"theorem\s+contender_10_lt_contender_11\s*:\s*contender_10\s*<\s*contender_11",
            proof_src,
        )),
        "strict comparison statement",
    )
    record(
        "audit checks closure hygiene",
        "#assert_not_in_closure11 BusyLean.contender_11" in AUDIT.read_text(encoding="utf-8"),
        "kernel-side transitive dependency audit supplied",
    )

    return {
        "status": "passed" if not failures else "failed",
        "scope": "static source audit only; not parsing/elaboration/kernel checking",
        "files": file_info,
        "checks": checks,
        "failures": failures,
    }


if __name__ == "__main__":
    result = audit()
    print(json.dumps(result, indent=2, sort_keys=True))
    sys.exit(0 if result["status"] == "passed" else 1)
