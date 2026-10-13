#!/usr/bin/env python3
"""Verify pinned upstream bytes and scan new source. Not a Lean kernel audit."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
COMMIT = "86b360648163f0249eab79539438b6a83dfe8215"
UPSTREAM = {
 "BigNumber/Definitions.lean": (
  "proposals/P5-w-reflection/lean/BigNumber/Definitions.lean",
  "0cb1e14966d62d4c17302f8f6b41316fb4181a42"),
 "BusyLean/Reflection.lean": (
  "BusyLean/Reflection.lean", "2703943ffe1207bd398d5f750daadff8139c5418"),
 "BusyLean/Contender6.lean": (
  "BusyLean/Contender6.lean", "248aa97049d0045b9635bb816842870d4a19eaed")}

def code_only(text: str) -> str:
    """Erase nested Lean block comments, line comments and double-quoted strings."""
    out: list[str] = []
    i = depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\": i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
            out.append(" ")
        else:
            out.append(text[i]); i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)

def main() -> int:
    manifest: dict = {"repository": "https://github.com/VladimirReshetnikov/BusyLean",
                     "commit": COMMIT, "vendored_files": []}
    errors: list[str] = []
    for local, (remote, expected) in UPSTREAM.items():
        data = (ROOT / "lean" / local).read_bytes()
        blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        manifest["vendored_files"].append({"local_path": "lean/" + local,
            "upstream_path": remote, "bytes": len(data), "git_blob_sha1": blob,
            "expected_git_blob_sha1": expected,
            "sha256": hashlib.sha256(data).hexdigest(), "exact_match": blob == expected})
        if blob != expected: errors.append(f"Upstream hash mismatch: {local}")
    banned = r"\b(sorry|admit|axiom|noncomputable|partial|unsafe|opaque|implemented_by|extern|native_decide)\b"
    files = sorted((ROOT / "lean").rglob("*.lean"))
    for path in files:
        code = code_only(path.read_text(encoding="utf-8"))
        for match in re.finditer(banned, code):
            errors.append(f"Forbidden token {match.group(0)} in {path.relative_to(ROOT)}")
    # This lexical check intentionally does NOT claim transitive closure verification.
    model = code_only((ROOT / "lean/Mirror/Model.lean").read_text())
    banned_names = ["BusyLean.contender_6", "BusyLean.finalFamily", "BusyLean.index",
                    "BigNumber.contender_6", "boostProgram", "numberProgram"]
    for name in banned_names:
        if name in model: errors.append(f"Direct forbidden dependency in Model.lean: {name}")
    result = {"status": "PASS" if not errors else "FAIL", "errors": errors,
              "lean_files_scanned": len(files), "exact_upstream_files": len(UPSTREAM),
              "kernel_checked": False,
              "transitive_dependency_audit": "NOT_RUN; see Mirror/Audit.lean",
              "scope": "Git blob hashes, lexical exclusions, direct Model.lean names only"}
    (ROOT / "evidence/SOURCE_MANIFEST.json").write_text(json.dumps(manifest, indent=2)+"\n")
    (ROOT / "evidence/source_audit.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
    return int(bool(errors))

if __name__ == "__main__":
    sys.exit(main())
