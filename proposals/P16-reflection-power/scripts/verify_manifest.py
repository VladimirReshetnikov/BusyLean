#!/usr/bin/env python3
"""Verify MANIFEST.sha256 from the package root."""
from __future__ import annotations
import hashlib
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
manifest = root / "MANIFEST.sha256"
if not manifest.exists():
    raise SystemExit("MANIFEST.sha256 is missing")
errors = []
count = 0
for line in manifest.read_text(encoding="utf-8").splitlines():
    if not line.strip():
        continue
    digest, rel = line.split("  ", 1)
    path = root / rel
    count += 1
    if not path.is_file():
        errors.append(f"missing: {rel}")
        continue
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != digest:
        errors.append(f"digest mismatch: {rel}")
if errors:
    print("MANIFEST FAIL")
    print("\n".join(errors))
    sys.exit(1)
print(f"MANIFEST PASS ({count} files)")
