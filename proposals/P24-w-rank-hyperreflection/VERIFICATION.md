# Verification ledger

## Completed in this artifact environment

- Repository interfaces inspected at BusyLean base commit
  `64d31a0cf6f1aa4477a088be5554957de6e87a61`.
- Three main Lean modules checked by `scripts/static_audit.py`:
  balanced delimiters, no forbidden shortcut tokens, SHA-256 digests, file
  sizes, and maximum line lengths. Result: **PASS**.
- The mathematical comparison was reviewed as three explicit strict
  inequalities, each using an existing occurrence theorem rather than oracle
  monotonicity.
- `article/contender20.tex` compiled with `pdflatex`/`latexmk` to a 25-page PDF.
- Final LaTeX log: no overfull boxes, underfull boxes, undefined references, or
  LaTeX warnings.
- The final PDF was rendered at 150 dpi; all 25 pages were visually inspected
  for clipping, overlap, missing glyphs, and layout failures.
- Integration patch, architecture graph, focused smoke test, and focused axiom
  and closure audit are included.
- `integration/contender20.patch` passed `git apply --check` and a full apply
  against a reconstructed copy of the exact touched base-file contexts.

## Not completed here

The runtime contained neither `lean` nor `lake`, and outbound shell networking
was unavailable. Consequently the new Lean files have **not** been elaborated
or kernel-checked in this environment. No build-time, axiom-list, or dependency-
closure result is claimed as measured.

## Required acceptance commands

Run these from a BusyLean checkout at the recorded base commit after applying
`integration/contender20.patch`:

```bash
python3 scripts/static_audit.py
lake build BusyLean.Contender20
lake build BusyLean.Comparison20
lake env lean test/Contender20Smoke.lean
lake env lean test/Audit20.lean
```

Then update `scripts/check.py` as documented and run the repository-wide clean
budget/audit script. Any elaboration repair should preserve the definitions;
the likeliest issues, if any, are shallow definitional-equality annotations in
`spliceLifts` or implicit-argument inference in the recursive proof.
