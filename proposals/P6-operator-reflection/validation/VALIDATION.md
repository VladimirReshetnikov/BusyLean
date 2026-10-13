# Validation report

## Scope

- Project: BusyLean Contender 7 research bundle
- Base repository revision: `86b360648163f0249eab79539438b6a83dfe8215`
- Intended toolchain: Lean 4.34.0
- Preparation date: 2026-10-12 (America/Los_Angeles)

## Completed checks

### Lean source, static

`python3 scripts/static_audit.py` passed. It checked:

- all six new Lean/test files are present;
- no excluded source tokens occur after comments are removed;
- the definition layer does not mention `contender_6`;
- required definitions and theorem names are present;
- the expected transitive comparison chain is present; and
- `BusyLean.lean` imports all four new modules.

Output: `static_audit_output.txt`.

### Patch integrity

`patches/contender7.patch` was generated from the exact original
`BusyLean.lean` content at the base revision plus the new files. It passed
`git apply --check` in a clean temporary Git repository and was then applied
successfully there.

### Executable explanatory model

`python3 scripts/ordinal_skeleton.py` passed its finite-height regression tests.
This script illustrates the paper's exponent bookkeeping; it is explicitly not
a formal ordinal proof.

Output: `ordinal_skeleton_output.txt`.

### Python

All Python scripts passed `python3 -m py_compile`.

### Article and PDF

- `article/contender7.tex` compiled with `pdflatex` in two clean passes.
- The synchronized final PDF has 21 pages; metadata is recorded in
  `pdf_inspect.txt`.
- The PDF was rendered to PNG at 160 dpi using the PDF skill renderer.
- A contact sheet and selected full-size pages were visually inspected.
- No clipping, overlapping text, black replacement glyphs, or broken code
  listings were observed.
- `pdftotext` recovered the title, the strict comparison statement, the
  `lambda^lambda` heuristic disclaimer, and the kernel-validation disclaimer.

## Not completed in this environment

The environment has neither `lean`, `lake`, nor `elan`, and outbound network
access is unavailable. Therefore the following are not claimed:

- Lean kernel acceptance of the new source;
- generated-code acceptance of the two higher-order structural recursions;
- the exact axiom report on Lean 4.34.0;
- compliance with the 15-second definition budget; or
- compliance with the 60-second proof budget.

The supplied `scripts/check_contender7.py` performs these decisive checks after
integration. Until it passes, the Lean development should be described as a
carefully reviewed proposal with proof source, not as a kernel-verified accepted
contender.

## Required integration command

From a BusyLean checkout at the recorded revision:

```bash
git apply patches/contender7.patch
python3 scripts/check_contender7.py
```

The script performs clean definition and proof builds, runs the recursion smoke
test, runs the axiom audit, and executes the transitive dependency-closure audit
embedded in `test/Contender7Audit.lean`.
