#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
python3 "$ROOT/scripts/static_audit.py" | tee "$ROOT/logs/static_audit.txt"
python3 "$ROOT/scripts/finite_model.py" | tee "$ROOT/logs/finite_model.txt"
python3 "$ROOT/scripts/ordinal_calibration.py" | tee "$ROOT/logs/ordinal_calibration.txt"
