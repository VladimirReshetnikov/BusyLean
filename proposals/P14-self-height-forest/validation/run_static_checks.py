#!/usr/bin/env python3
"""Artifact-level checks that do not substitute for Lean kernel replay."""
from __future__ import annotations

import py_compile
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEF = ROOT / "lean" / "BusyLean" / "Contender11.lean"
CMP = ROOT / "lean" / "BusyLean" / "Comparison11.lean"
AUDIT = ROOT / "lean" / "test" / "Audit11.lean"
CHECKER = ROOT / "lean" / "scripts" / "check_contender11.py"
PATCH = ROOT / "patches" / "contender11.patch"
TEX = ROOT / "article" / "contender11.tex"
PDF = ROOT / "article" / "contender11.pdf"


def run(args: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True, check=False)


def strip_lean_comments_and_strings(text: str) -> str:
    """Remove nested block comments, line comments, and strings for token scans."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            in_string = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"FAIL: {message}")
    print(f"PASS: {message}")


def main() -> None:
    for path in [DEF, CMP, AUDIT, CHECKER, PATCH, TEX, PDF]:
        require(path.is_file() and path.stat().st_size > 0, f"present: {path.relative_to(ROOT)}")

    def_code = strip_lean_comments_and_strings(DEF.read_text(encoding="utf-8"))
    cmp_code = strip_lean_comments_and_strings(CMP.read_text(encoding="utf-8"))

    forbidden = [
        "noncomputable", "partial", "unsafe", "opaque", "implemented_by",
        "extern", "native_decide", "sorry", "admit", "axiom",
    ]
    for token in forbidden:
        require(not re.search(rf"\b{re.escape(token)}\b", def_code),
                f"definition code avoids forbidden token `{token}`")
    for token in ["sorry", "admit", "axiom"]:
        require(not re.search(rf"\b{re.escape(token)}\b", cmp_code),
                f"comparison code avoids proof placeholder `{token}`")

    prior_constants = [f"contender_{n}" for n in range(5, 11)]
    for token in prior_constants:
        require(not re.search(rf"\b{re.escape(token)}\b", def_code),
                f"definition code does not reference closed prior constant `{token}`")

    for name in ["reflect11", "towerFk", "diagonal11", "stage11", "family10", "F11", "contender_11"]:
        require(re.search(rf"\bdef\s+{re.escape(name)}\b", def_code) is not None,
                f"definition `{name}` exists")
    for name in [
        "towerFk_strictMono", "fixedTower_lt_diagonal11", "family10_lt_F11",
        "contender_10_lt_contender_11", "defined_tree_eventually_lt11",
    ]:
        require(re.search(rf"\btheorem\s+{re.escape(name)}\b", cmp_code) is not None,
                f"theorem script `{name}` exists")

    py_compile.compile(str(CHECKER), doraise=True)
    require(True, "Python checker syntax compiles")

    baseline = """import BusyLean.Contender5
import BusyLean.PortAgreement
import BusyLean.Reflection
import BusyLean.ReflectionFacts
import BusyLean.Contender6
import BusyLean.Comparison
import BusyLean.Contender7
import BusyLean.Comparison7
import BusyLean.Contender8
import BusyLean.Comparison8
import BusyLean.Contender9
import BusyLean.Comparison9
import BusyLean.Contender10
import BusyLean.Comparison10
"""
    with tempfile.TemporaryDirectory(prefix="contender11-patch-") as tmp_s:
        tmp = Path(tmp_s)
        (tmp / "BusyLean.lean").write_text(baseline, encoding="utf-8")
        init = run(["git", "init", "-q"], tmp)
        require(init.returncode == 0, "temporary Git skeleton initialized")
        checked = run(["git", "apply", "--check", str(PATCH)], tmp)
        require(checked.returncode == 0, "integration patch passes `git apply --check`")
        applied = run(["git", "apply", str(PATCH)], tmp)
        require(applied.returncode == 0, "integration patch applies cleanly")
        comparisons = {
            tmp / "BusyLean" / "Contender11.lean": DEF,
            tmp / "BusyLean" / "Comparison11.lean": CMP,
            tmp / "test" / "Audit11.lean": AUDIT,
            tmp / "scripts" / "check_contender11.py": CHECKER,
        }
        for patched, source in comparisons.items():
            require(patched.read_bytes() == source.read_bytes(),
                    f"patched file matches archive source: {source.relative_to(ROOT)}")
        root_text = (tmp / "BusyLean.lean").read_text(encoding="utf-8")
        require(root_text.endswith("import BusyLean.Contender11\nimport BusyLean.Comparison11\n"),
                "root module imports Contender 11 modules")

    info = run(["pdfinfo", str(PDF)])
    require(info.returncode == 0, "PDF metadata is readable")
    page_match = re.search(r"^Pages:\s+(\d+)$", info.stdout, re.MULTILINE)
    require(page_match is not None and int(page_match.group(1)) >= 15,
            "PDF has at least 15 pages")

    with tempfile.NamedTemporaryFile(suffix=".txt") as out:
        text_result = run(["pdftotext", str(PDF), out.name])
        require(text_result.returncode == 0, "PDF text extraction succeeds")
        pdf_text = Path(out.name).read_text(encoding="utf-8", errors="replace")
    for phrase in [
        "Self-Height Diagonal Forest Closure",
        "contender_10 < contender_11",
        "Verification status",
        "Further research questions",
    ]:
        require(phrase in pdf_text, f"PDF contains expected phrase: {phrase}")

    latex_log = ROOT / "validation" / "latex_build.log"
    require(latex_log.is_file(), "final LaTeX log is present")
    log_text = latex_log.read_text(encoding="utf-8", errors="replace")
    require("Fatal error" not in log_text, "final LaTeX pass has no fatal error")
    require("undefined references" not in log_text.lower(), "final LaTeX pass has no undefined references")
    require("Overfull \\hbox" not in log_text, "final LaTeX pass has no overfull boxes")

    print("PASS: all artifact-level static checks completed")
    print("NOTE: these checks do not replace `python3 scripts/check_contender11.py` under Lean 4.34.0")


if __name__ == "__main__":
    main()
