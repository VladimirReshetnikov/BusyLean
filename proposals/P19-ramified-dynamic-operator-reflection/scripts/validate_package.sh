#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

required=(
  BusyLean/Contender14.lean
  BusyLean/Comparison14.lean
  test/Contender14Audit.lean
  article/contender14_rdor.tex
  article/contender14_rdor.pdf
  patches/integration.patch
  scripts/apply_overlay.sh
  scripts/check_in_repo.sh
  scripts/static_audit.py
  README.md
  VERIFICATION_STATUS.md
)
for f in "${required[@]}"; do
  test -s "$f" || { echo "missing or empty: $f" >&2; exit 1; }
done

bash -n scripts/apply_overlay.sh scripts/check_in_repo.sh scripts/validate_package.sh
python3 -m py_compile scripts/static_audit.py scripts/make_integration_patch.py
python3 scripts/static_audit.py

pages="$(pdfinfo article/contender14_rdor.pdf | awk '/^Pages:/ {print $2}')"
test "$pages" = "17" || { echo "unexpected PDF page count: $pages" >&2; exit 1; }

if grep -Eq '(^!|Overfull|Underfull)' artifacts/latex_build.log; then
  echo "LaTeX log contains a fatal or box diagnostic" >&2
  exit 1
fi

echo "PASS: package preflight (not a Lean kernel check)"
