#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../article"
for pass in 1 2 3; do
  echo "LuaLaTeX pass ${pass}/3"
  lualatex -interaction=nonstopmode -halt-on-error ramified_kind_reflection.tex
done
