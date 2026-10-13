#!/usr/bin/env bash
set -euo pipefail

# Run from the root of a BusyLean checkout after copying this overlay into it.
lake build BusyLean.Contender20
lake build BusyLean.Comparison20
lake env lean test/Contender20Smoke.lean
lake env lean test/Audit20.lean
