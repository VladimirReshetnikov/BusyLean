#!/usr/bin/env bash
set -euo pipefail

# Run from the root of a BusyLean checkout after applying the overlay.
if [[ ! -f BusyLean/Contender14.lean || ! -f BusyLean/Comparison14.lean ]]; then
  echo "run this command from an integrated BusyLean repository root" >&2
  exit 2
fi

python3 scripts/check.py
lake env lean test/Contender14Audit.lean
