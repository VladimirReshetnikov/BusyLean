#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 /path/to/BusyLean" >&2
  exit 2
fi

BUSYLEAN=$(cd "$1" && pwd)
ARCHIVE_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

rsync -a "$ARCHIVE_ROOT/lean/" "$BUSYLEAN/"
cd "$BUSYLEAN"
python3 scripts/check.py
