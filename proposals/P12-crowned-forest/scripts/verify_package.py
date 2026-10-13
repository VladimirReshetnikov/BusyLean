#!/usr/bin/env python3
"""Verify package-local artifacts without claiming a Lean kernel check."""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run_json(script: str) -> dict:
    p = subprocess.run([sys.executable, str(ROOT / "scripts" / script)],
                       text=True, capture_output=True)
    if p.returncode != 0:
        raise RuntimeError(f"{script} failed:\n{p.stdout}\n{p.stderr}")
    return json.loads(p.stdout)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def verify_sums() -> tuple[int, list[str]]:
    manifest = ROOT / "SHA256SUMS"
    if not manifest.exists():
        return 0, ["SHA256SUMS is absent"]
    failures: list[str] = []
    count = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, rel = line.split("  ", 1)
        path = ROOT / rel
        count += 1
        if not path.is_file():
            failures.append(f"missing: {rel}")
        elif sha256(path) != expected:
            failures.append(f"hash mismatch: {rel}")
    return count, failures


def main() -> int:
    static = run_json("static_audit.py")
    reference = run_json("reference_model.py")
    pdf = json.loads((ROOT / "evidence" / "pdf_validation.json").read_text())
    lean = json.loads((ROOT / "evidence" / "lean_validation.json").read_text())
    count, hash_failures = verify_sums()
    status = (
        static.get("status") == "passed"
        and reference.get("status") == "passed"
        and pdf.get("status") == "passed"
        and not hash_failures
    )
    report = {
        "status": "passed" if status else "failed",
        "kernel_validation": lean.get("status"),
        "static_audit": static.get("status"),
        "reference_model": reference.get("status"),
        "reference_assertions": reference.get("assertions"),
        "pdf_validation": pdf.get("status"),
        "pdf_pages": pdf.get("pages"),
        "sha256_entries_checked": count,
        "sha256_failures": hash_failures,
        "warning": "Package-local verification is not a Lean kernel check.",
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if status else 1


if __name__ == "__main__":
    raise SystemExit(main())
