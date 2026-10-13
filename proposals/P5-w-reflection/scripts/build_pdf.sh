#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../article"
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
