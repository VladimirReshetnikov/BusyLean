#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/article"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error ramified_semantic_worlds.tex
 done
