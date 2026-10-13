#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../article"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error contender7.tex > "../evidence/pdf_pass_${pass}.log"
done
