#!/usr/bin/env bash
set -euo pipefail

# Apply the Contender 14 overlay to a BusyLean checkout.
# Run this script from the root of the target BusyLean repository.

ROOT=$(pwd)
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

if [[ ! -f "$ROOT/BusyLean.lean" || ! -d "$ROOT/BusyLean" ]]; then
  echo "error: run from the BusyLean repository root" >&2
  exit 1
fi

cp "$HERE/overlay/BusyLean/HyperReflection.lean" "$ROOT/BusyLean/"
cp "$HERE/overlay/BusyLean/HyperReflectionFacts.lean" "$ROOT/BusyLean/"
cp "$HERE/overlay/BusyLean/Contender14.lean" "$ROOT/BusyLean/"
cp "$HERE/overlay/BusyLean/Comparison14.lean" "$ROOT/BusyLean/"
mkdir -p "$ROOT/test" "$ROOT/scripts" "$ROOT/.github/workflows"
cp "$HERE/overlay/test/Contender14Audit.lean" "$ROOT/test/"
cp "$HERE/overlay/scripts/check_contender14.py" "$ROOT/scripts/"
cp "$HERE/overlay/.github/workflows/validate-contender14.yml" \
  "$ROOT/.github/workflows/"

python3 - "$ROOT/BusyLean.lean" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
imports = """import BusyLean.HyperReflection
import BusyLean.HyperReflectionFacts
import BusyLean.Contender14
import BusyLean.Comparison14
"""
if "import BusyLean.Comparison14" not in text:
    anchor = "import BusyLean.Comparison13\n"
    if anchor not in text:
        raise SystemExit("could not find Comparison13 import in BusyLean.lean")
    text = text.replace(anchor, anchor + imports)
    path.write_text(text, encoding="utf-8")
PY

echo "Contender 14 overlay applied."
echo "Run: python3 scripts/check_contender14.py"
