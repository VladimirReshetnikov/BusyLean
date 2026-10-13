# Validation ledger

## Completed in this environment

- Audited the upstream repository at commit
  `86b360648163f0249eab79539438b6a83dfe8215`.
- Confirmed the pinned toolchain is Lean `v4.34.0`.
- Ran the textual banned-construct and dependency audit.
- Ran an executable finite model of seed domination, strict order growth, and
  the leaf-to-index comparison chain.
- Generated and checked the ordinal-calibration ledger.
- Compiled the LaTeX article with `pdflatex`.
- Rendered every PDF page and inspected the rasterized output for clipping and
  broken glyphs.

## Not completed in this environment

The Lean source was not checked by a Lean kernel here because no Lean executable
was installed and the available external runtime artifacts could not be fetched
through the environment's binary-download limits.  Accordingly, this archive
does **not** claim kernel verification.  It supplies:

1. compact source designed against the exact upstream APIs;
2. a kernel-side closure/axiom audit file;
3. a pinned GitHub Actions workflow for Lean 4.34.0;
4. an explicit list of the commands required for final acceptance.

The status should be upgraded to `kernel checked` only after both `lake build`
and `lake env lean test/Contender7Audit.lean` succeed on the pinned toolchain.
