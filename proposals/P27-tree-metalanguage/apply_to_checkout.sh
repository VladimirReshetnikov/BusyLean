#!/usr/bin/env bash
set -euo pipefail

PACKAGE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGET="${1:-.}"

if [[ ! -f "$TARGET/lakefile.toml" || ! -f "$TARGET/BusyLean.lean" ]]; then
  echo "error: '$TARGET' does not look like the BusyLean repository root" >&2
  exit 2
fi

install -D -m 0644 \
  "$PACKAGE_ROOT/BusyLean/Ordinal/TreeLanguage4.lean" \
  "$TARGET/BusyLean/Ordinal/TreeLanguage4.lean"
install -D -m 0644 \
  "$PACKAGE_ROOT/BusyLean/Contender35.lean" \
  "$TARGET/BusyLean/Contender35.lean"
install -D -m 0644 \
  "$PACKAGE_ROOT/BusyLean/Comparison35.lean" \
  "$TARGET/BusyLean/Comparison35.lean"
install -D -m 0644 \
  "$PACKAGE_ROOT/test/Contender35Audit.lean" \
  "$TARGET/test/Contender35Audit.lean"

if ! grep -q '^import BusyLean.Ordinal.TreeLanguage4$' "$TARGET/BusyLean.lean"; then
  cat >> "$TARGET/BusyLean.lean" <<'IMPORTS'
import BusyLean.Ordinal.TreeLanguage4
import BusyLean.Contender35
import BusyLean.Comparison35
IMPORTS
fi

cat <<'MSG'
Contender 35 files installed.

Recommended verification:
  lake build BusyLean.Ordinal.TreeLanguage4
  lake build BusyLean.Contender35
  lake build BusyLean.Comparison35
  lake env lean test/Contender35Audit.lean

Never evaluate BusyLean.contender_35.
MSG
