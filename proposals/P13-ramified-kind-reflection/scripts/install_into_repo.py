#!/usr/bin/env python3
"""Idempotently install the Contender 11 proposal into a BusyLean checkout."""
from __future__ import annotations

import argparse
import shutil
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent.parent

IMPORT_BLOCK = "import BusyLean.Contender11\nimport BusyLean.Comparison11\n"
AUDIT_BLOCK = r'''

-- Proposed Contender 11: diagonal ramified kind-reflection.
#print axioms BusyLean.contender_11
#print axioms BusyLean.contender_10_lt_contender_11
#print axioms BusyLean.family10_lt_F11
#print axioms BusyLean.fixed_rank_eventually_lt_F11
#print axioms BusyLean.fvalue_lt_F11
#print axioms BusyLean.RK.ramified_dominates
#print axioms BusyLean.RK.ramified_lt_of_lt

#assert_not_in_closure BusyLean.contender_11 :
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_10_lt_contender_11
#check @BusyLean.fixed_rank_eventually_lt_F11
#check @BusyLean.fvalue_lt_F11
#check @BusyLean.RK.ramified_level_lt
'''


def write(path: Path, content: str, dry_run: bool) -> None:
    if dry_run:
        print(f"would write {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    print(f"wrote {path}")


def copy(source: Path, target: Path, dry_run: bool) -> None:
    if dry_run:
        print(f"would copy {source} -> {target}")
        return
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
    print(f"copied {target}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    repo = args.repo.resolve()

    required = [
        repo / "BusyLean.lean",
        repo / "scripts" / "check.py",
        repo / "test" / "Audit.lean",
        repo / "BusyLean" / "Contender10.lean",
    ]
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        raise SystemExit("Not a compatible BusyLean checkout:\n  " + "\n  ".join(missing))

    copy(
        PACKAGE / "lean" / "BusyLean" / "Contender11.lean",
        repo / "BusyLean" / "Contender11.lean",
        args.dry_run,
    )
    copy(
        PACKAGE / "lean" / "BusyLean" / "Comparison11.lean",
        repo / "BusyLean" / "Comparison11.lean",
        args.dry_run,
    )
    copy(
        PACKAGE / "lean" / "test" / "Contender11Audit.lean",
        repo / "test" / "Contender11Audit.lean",
        args.dry_run,
    )
    copy(
        PACKAGE / "scripts" / "check_contender11.py",
        repo / "scripts" / "check_contender11.py",
        args.dry_run,
    )

    umbrella = repo / "BusyLean.lean"
    umbrella_text = umbrella.read_text(encoding="utf-8")
    if "import BusyLean.Contender11" not in umbrella_text:
        if not umbrella_text.endswith("\n"):
            umbrella_text += "\n"
        umbrella_text += IMPORT_BLOCK
        write(umbrella, umbrella_text, args.dry_run)
    else:
        print(f"already updated {umbrella}")

    checker = repo / "scripts" / "check.py"
    checker_text = checker.read_text(encoding="utf-8")
    updated = checker_text.replace(
        'PREVIOUS = "BusyLean.Comparison9"',
        'PREVIOUS = "BusyLean.Comparison10"',
    ).replace(
        'CURRENT_DEF = "BusyLean.Contender10"',
        'CURRENT_DEF = "BusyLean.Contender11"',
    )
    if updated == checker_text and "BusyLean.Contender11" not in checker_text:
        raise SystemExit("scripts/check.py did not match the expected Contender 10 version")
    if updated != checker_text:
        write(checker, updated, args.dry_run)
    else:
        print(f"already updated {checker}")

    audit = repo / "test" / "Audit.lean"
    audit_text = audit.read_text(encoding="utf-8")
    marker = "-- The statements, for the record."
    if "#print axioms BusyLean.contender_11" not in audit_text:
        if marker not in audit_text:
            raise SystemExit("test/Audit.lean lacks the expected insertion marker")
        audit_text = audit_text.replace(marker, AUDIT_BLOCK + "\n" + marker, 1)
        write(audit, audit_text, args.dry_run)
    else:
        print(f"already updated {audit}")

    print("installation edits complete")


if __name__ == "__main__":
    main()
