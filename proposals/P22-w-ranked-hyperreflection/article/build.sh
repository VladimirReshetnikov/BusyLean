#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error contender20_w_ranked.tex
