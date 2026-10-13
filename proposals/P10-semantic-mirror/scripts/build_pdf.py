#!/usr/bin/env python3
"""Compile the user-requested LaTeX report; retain logs outside article/."""
from __future__ import annotations
import json
from pathlib import Path
import shutil
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[1]

def main() -> int:
    engine = shutil.which("pdflatex")
    if engine is None:
        print("pdflatex is required", file=sys.stderr)
        return 2
    article = ROOT / "article"
    build = article / ".build"
    build.mkdir(exist_ok=True)
    logs: list[str] = []
    for run in range(3):
        cmd = [engine, "-interaction=nonstopmode", "-halt-on-error",
               "-output-directory=" + str(build), "semantic_mirror.tex"]
        p = subprocess.run(cmd, cwd=article, text=True, capture_output=True, timeout=90)
        logs.append(f"RUN {run + 1}\n{p.stdout}\n{p.stderr}")
        if p.returncode:
            (ROOT / "evidence/pdf_build.log").write_text("\n".join(logs))
            print(p.stdout[-5000:], file=sys.stderr)
            return 1
    shutil.copy2(build / "semantic_mirror.pdf", article / "semantic_mirror.pdf")
    (ROOT / "evidence/pdf_build.log").write_text("\n".join(logs))
    print(article / "semantic_mirror.pdf")
    return 0

if __name__ == "__main__":
    sys.exit(main())
