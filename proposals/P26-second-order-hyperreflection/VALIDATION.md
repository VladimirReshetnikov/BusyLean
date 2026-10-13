# Validation record

## Baseline audit

The design was based on the BusyLean `main` tree
`64d31a0cf6f1aa4477a088be5554957de6e87a61` (retrieved 2026-10-13). The
incumbent API used by the overlay is:

- `Transformer`, `TransformerLift`, `stageLift`, `diagonalLift`;
- `Progressive`, `PreservesProgressive`, `StrictlyInflationary`;
- `stageLift_progressive`, `base_lt_stageLift`;
- `diagonalLift_preservesProgressive`,
  `diagonalLift_strictlyInflationary`;
- `lTransformer`, `lTransformer_progressive`;
- `F19`, `family18`, `schedule19`, `rank19`, and `input_lt_F19`.

## Checks performed here

1. The source-hygiene audit completed with status `PASS`.
2. No executable Lean source contains `sorry`, `admit`, an `axiom`
   declaration, `noncomputable`, `unsafe`, `partial`, `opaque`, `extern`,
   `implemented_by`, or `Classical.choice`.
3. Expected declarations and module dependency edges are present.
4. The LaTeX source compiled successfully with `pdflatex`/`latexmk`.
5. The resulting PDF was rendered to page images and visually inspected for
   clipping, missing glyphs, and broken listings.
6. SHA-256 checksums were generated for all final package files.

## Check not performed here

A Lean 4.34.0 toolchain was not installed in the execution environment, and
network installation of the 4.34.0 binary was unavailable. Therefore this
package does not claim an executed kernel check. The exact commands required
for that check are in `INTEGRATION.md`.

## Proof-risk assessment

The new proofs are parametric and mirror the already accepted first-order
proofs in `HyperReflectionFacts.lean`. They do not unfold `family19`, `F20`, or
`contender_20`. The main residual risks are elaboration details in:

- structural recursion for `stageHyperLift_good` and
  `base_lt_stageHyperLift`;
- definitional reduction of `spliceLifts` in one `change` statement;
- implicit argument inference in applications of the generic strictness
  predicates.

These are local, non-mathematical risks. No theorem depends on an unproved
monotonicity property of oracle reflection.
