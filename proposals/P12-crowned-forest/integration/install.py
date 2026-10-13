#!/usr/bin/env python3
"""Idempotent installer for the Contender 11 proposal.

Default mode is a dry run.  Pass --apply only after reviewing the proposed
changes.  The script requires the pinned BusyLean commit unless explicitly
overridden.
"""
from __future__ import annotations

import argparse
import difflib
import shutil
import subprocess
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent.parent
PINNED = "4c4b03d0e2003c479e3bee90a21c8bea13f66c40"

IMPORT_BLOCK = "import BusyLean.Contender11\nimport BusyLean.Comparison11\n"
AUDIT_BLOCK = (PACKAGE / "candidate" / "test" / "Audit.lean.append").read_text(encoding="utf-8")


def head(repo: Path) -> str | None:
    p = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, text=True,
                       capture_output=True)
    return p.stdout.strip() if p.returncode == 0 else None


def update_text(path: Path, transform, apply: bool) -> None:
    old = path.read_text(encoding="utf-8")
    new = transform(old)
    if old == new:
        print(f"unchanged: {path}")
        return
    print("".join(difflib.unified_diff(
        old.splitlines(True), new.splitlines(True),
        fromfile=str(path), tofile=str(path),
    )))
    if apply:
        path.write_text(new, encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--allow-different-head", action="store_true")
    args = ap.parse_args()
    repo = args.repo.resolve()
    observed = head(repo)
    if observed != PINNED and not args.allow_different_head:
        raise SystemExit(
            f"expected {PINNED}, found {observed}; inspect drift or pass "
            "--allow-different-head"
        )

    for rel in ["BusyLean/Contender11.lean", "BusyLean/Comparison11.lean"]:
        src = PACKAGE / "candidate" / rel
        dst = repo / rel
        if dst.exists() and dst.read_bytes() != src.read_bytes():
            raise SystemExit(f"refusing to overwrite differing file {dst}")
        print(f"{'copy' if args.apply else 'would copy'}: {src} -> {dst}")
        if args.apply:
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)

    def add_imports(text: str) -> str:
        if "import BusyLean.Contender11" in text:
            return text
        if not text.endswith("\n"):
            text += "\n"
        return text + IMPORT_BLOCK

    update_text(repo / "BusyLean.lean", add_imports, args.apply)

    def add_audit(text: str) -> str:
        if "#print axioms BusyLean.contender_11" in text:
            return text
        marker = "-- The final family is a genuine computable function"
        pos = text.find(marker)
        if pos < 0:
            return text.rstrip() + "\n" + AUDIT_BLOCK + "\n"
        return text[:pos] + AUDIT_BLOCK + "\n" + text[pos:]

    update_text(repo / "test" / "Audit.lean", add_audit, args.apply)

    def update_checker(text: str) -> str:
        text = text.replace(
            'PREVIOUS = "BusyLean.Comparison9"',
            'PREVIOUS = "BusyLean.Comparison10"',
        )
        text = text.replace(
            'CURRENT_DEF = "BusyLean.Contender10"',
            'CURRENT_DEF = "BusyLean.Contender11"',
        )
        return text

    update_text(repo / "scripts" / "check.py", update_checker, args.apply)

    for rel in ["Audit11.lean", "Contender11Smoke.lean"]:
        src = PACKAGE / "candidate" / "test" / rel
        dst = repo / "test" / rel
        if dst.exists() and dst.read_bytes() != src.read_bytes():
            raise SystemExit(f"refusing to overwrite differing file {dst}")
        print(f"{'copy' if args.apply else 'would copy'}: {src} -> {dst}")
        if args.apply:
            shutil.copy2(src, dst)

    mode = "applied" if args.apply else "dry run only"
    print(f"installation plan {mode}; pinned baseline {PINNED}")


if __name__ == "__main__":
    main()
