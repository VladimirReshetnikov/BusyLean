#!/usr/bin/env bash
set -euo pipefail

# Validate an already-patched BusyLean checkout.
# Usage:
#   ./scripts/build_and_audit.sh /path/to/BusyLean
# Set FULL_BUILD=1 to add the complete library build and existing repository audit.

PACKAGE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="${1:-$PWD}"

if [[ ! -f "$REPO_ROOT/lakefile.toml" || ! -f "$REPO_ROOT/lean-toolchain" ]]; then
  echo "error: '$REPO_ROOT' is not a BusyLean project root" >&2
  echo "usage: $0 /path/to/patched/BusyLean" >&2
  exit 2
fi

(
  cd "$REPO_ROOT"
  lake build BusyLean.Comparison20
  lake env lean test/SecondOrderReflectionSmoke.lean
)

python3 "$PACKAGE_ROOT/scripts/static_audit.py"

if [[ "${FULL_BUILD:-0}" == "1" ]]; then
  (
    cd "$REPO_ROOT"
    lake build
    lake env lean test/Audit.lean
  )
fi
