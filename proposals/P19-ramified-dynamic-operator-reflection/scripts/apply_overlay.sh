#!/usr/bin/env bash
set -euo pipefail

# Apply this archive as an idempotent overlay to a BusyLean checkout.
# Usage: ./scripts/apply_overlay.sh [--force] /path/to/BusyLean

EXPECTED_COMMIT="1ee50c7d97bbed57a60709f661453c3e213f4db3"
FORCE=0
if [[ ${1:-} == "--force" ]]; then
  FORCE=1
  shift
fi
if [[ $# -ne 1 ]]; then
  echo "usage: $0 [--force] /path/to/BusyLean" >&2
  exit 2
fi

SRC="$(cd "$(dirname "$0")/.." && pwd)"
DST="$(cd "$1" && pwd)"

if [[ ! -f "$DST/BusyLean.lean" || ! -f "$DST/scripts/check.py" || ! -f "$DST/test/Audit.lean" ]]; then
  echo "not a BusyLean repository root: $DST" >&2
  exit 2
fi

if command -v git >/dev/null 2>&1 && git -C "$DST" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  ACTUAL_COMMIT="$(git -C "$DST" rev-parse HEAD)"
  if [[ "$ACTUAL_COMMIT" != "$EXPECTED_COMMIT" && $FORCE -ne 1 ]]; then
    cat >&2 <<MSG
BusyLean checkout is at $ACTUAL_COMMIT, but this overlay targets
$EXPECTED_COMMIT.
Re-run with --force only after reviewing the diff and resolving API changes.
MSG
    exit 3
  fi
fi

install -m 0644 "$SRC/BusyLean/Contender14.lean" "$DST/BusyLean/Contender14.lean"
install -m 0644 "$SRC/BusyLean/Comparison14.lean" "$DST/BusyLean/Comparison14.lean"
install -m 0644 "$SRC/test/Contender14Audit.lean" "$DST/test/Contender14Audit.lean"
install -m 0644 "$SRC/article/contender14_rdor.tex" "$DST/article/contender14_rdor.tex"
install -m 0644 "$SRC/article/contender14_rdor.pdf" "$DST/article/contender14_rdor.pdf"

python3 - "$DST" "$SRC/patches/Audit14.append.lean" <<'PY'
from pathlib import Path
import sys

root = Path(sys.argv[1])
audit_block = Path(sys.argv[2]).read_text(encoding="utf-8").strip()

p = root / "BusyLean.lean"
s = p.read_text(encoding="utf-8")
needle = "import BusyLean.Comparison13\n"
insert = needle + "import BusyLean.Contender14\nimport BusyLean.Comparison14\n"
if "import BusyLean.Comparison14" not in s:
    if needle not in s:
        raise SystemExit("BusyLean.lean does not contain expected Comparison13 import")
    s = s.replace(needle, insert, 1)
    p.write_text(s, encoding="utf-8")

p = root / "scripts" / "check.py"
s = p.read_text(encoding="utf-8")
old_previous = 'PREVIOUS = "BusyLean.Comparison12"'
new_previous = 'PREVIOUS = "BusyLean.Comparison13"'
old_current = 'CURRENT_DEF = "BusyLean.Contender13"'
new_current = 'CURRENT_DEF = "BusyLean.Contender14"'
if new_previous not in s:
    if old_previous not in s:
        raise SystemExit("scripts/check.py has an unexpected PREVIOUS setting")
    s = s.replace(old_previous, new_previous, 1)
if new_current not in s:
    if old_current not in s:
        raise SystemExit("scripts/check.py has an unexpected CURRENT_DEF setting")
    s = s.replace(old_current, new_current, 1)
p.write_text(s, encoding="utf-8")

p = root / "test" / "Audit.lean"
s = p.read_text(encoding="utf-8")
if "#print axioms BusyLean.contender_14" not in s:
    if not s.endswith("\n"):
        s += "\n"
    s += "\n" + audit_block + "\n"
    p.write_text(s, encoding="utf-8")
PY

cat <<MSG
Contender 14 overlay installed in:
  $DST

Next commands:
  cd "$DST"
  python3 scripts/check.py
  lake env lean test/Contender14Audit.lean

Do not evaluate BusyLean.contender_14.
MSG
