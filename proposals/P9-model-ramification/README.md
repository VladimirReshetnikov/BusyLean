# BusyLean Contender 7: autonomous model ramification

**Pinned comparison:** `VladimirReshetnikov/BusyLean` commit
`86b360648163f0249eab79539438b6a83dfe8215`.

## Main mathematical result

Let `theta(x)` apply `y -> 2^y` exactly `x+1` times, starting at `x+1`.
The article proves

    theta^[46](BusyLean.contender_6) < BusyLean.contender_7.

The exponent `[46]` means function iteration, NOT ordinary exponentiation.
The candidate replaces a fixed reflector by an interpreter of lower reflectors,
forest recursors, and generated tree schedules; it then closes under finite
ramification and model-valued recursion along a schedule from the strengthened
language. Its definition does not call `BusyLean.contender_6`,
`BusyLean.finalFamily`, or `BigNumber.contender_6`.

**Validation boundary:** The mathematical proofs are in the article. The new
Lean definitions and 84 theorem scripts are **not compiler-checked** in this
package's authoring environment. No Lean compiler was available, and retrieval
attempts did not supply one. `evidence/lean_validation.json` says `not_run`.
Axiom closure and the contest's 15/60-second build budgets are unverified.
This is a research proposal, not an already certified contest submission.
There are no intentional proof placeholders. The 1,830 passing Python checks
and lexical audit do NOT substitute for a Lean kernel check.

## Files

- `article/contender7.tex`, `article/contender7.pdf`: 23-page article and compiled PDF.
- `lean/BusyLean7/`: new definitions, arithmetic, enumeration, semantics,
  reflection, quantitative comparison, selectors, and cofinality proof scripts.
- `lean/BigNumber/Definitions.lean`, `lean/BusyLean/Reflection.lean`, and
  `lean/BusyLean/Contender6.lean`: byte-identical pinned baseline files, checked
  against their Git blob hashes. No upstream compiled binaries are included.
- `test/`: proposed Lean smoke tests and transitive axiom/dependency audit.
- `python/`: guarded independent reference interpreter and finite tests.
- `scripts/`: reproducible checks and PDF build.
- `integration/Transitive.lean`: optional corollaries for C5 and proposal P5,
  requiring the full pinned repository's existing comparison modules.
- `evidence/`: actual validation receipts; `docs/` contains the audit boundary,
  integration instructions and source provenance.

## Run the available checks

    python3 python/test_reference.py
    python3 scripts/source_audit.py

With the pinned Lean toolchain installed:

    python3 scripts/check.py

The checker uses a clean build directory, checks definitions first, then proofs,
then small smoke tests and an axiom/dependency audit. It refuses to report a
pass for a missing compiler, failed proof, unexpected axiom, or exceeded budget.
It never evaluates either contender. A simple full build is also available:

    cd lean
    lake build BusyLean7

Build the PDF with `bash scripts/build_pdf.sh` (a standard LaTeX installation
with `pdflatex`, `lmodern`, `microtype`, `listings`, and `hyperref` is required).

## Scope

The direct comparison is against the adopted current C6. C5 and proposal P5
follow from the upstream theorems plus the new comparison. This package does
not claim an exact comparison against the separate P1-P4 proposal constants;
the upstream review's rankings are explicitly heuristic. It also does not
identify a proof-theoretic ordinal, prove an optimality claim, or assert a
universal interpreter for all Lean definitions.

**Never evaluate `BusyLean.contender_7` or `BusyLean.contender_6`.**

## Integrity

Run `python3 scripts/verify_package.py` to check the delivered source, article,
and evidence files against `SHA256SUMS`. This verifies file integrity only.
