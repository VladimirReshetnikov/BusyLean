#!/usr/bin/env python3
"""Verify every delivered file against SHA256SUMS; not a Lean proof check."""
from __future__ import annotations
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

def main() -> int:
    manifest = ROOT / "SHA256SUMS"
    if not manifest.is_file():
        print("Missing SHA256SUMS", file=sys.stderr)
        return 2
    failures: list[str] = []
    count = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split("  ", 1)
        path = (ROOT / relative).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file():
            failures.append(relative + ": missing or invalid path")
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        count += 1
        if actual != expected:
            failures.append(relative + ": hash mismatch")
    for message in failures:
        print(message, file=sys.stderr)
    print(f"Checked {count} file hashes; {len(failures)} failures.")
    return 1 if failures else 0

if __name__ == "__main__":
    raise SystemExit(main())
