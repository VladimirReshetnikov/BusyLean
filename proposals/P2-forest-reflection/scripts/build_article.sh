#!/usr/bin/env bash
set -euo pipefail
article_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../article" && pwd)"
cd "$article_root"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
