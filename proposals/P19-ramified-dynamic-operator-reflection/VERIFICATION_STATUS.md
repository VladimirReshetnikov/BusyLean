# Verification status

## Completed in the preparation environment

- Inspected the BusyLean main branch and fixed the baseline at commit
  `1ee50c7d97bbed57a60709f661453c3e213f4db3`.
- Matched the repository's `lean-toolchain` pin
  `leanprover/lean4:v4.34.0`.
- Audited the contest rules relevant to computability, axioms, timing, and the
  prohibition on using the predecessor constant as a shortcut.
- Wrote the two Lean overlay modules and a standalone audit module.
- Ran `scripts/static_audit.py`; it passed all source-level checks and recorded
  hashes of the principal modules.
- Compiled `article/contender14_rdor.tex` to a 17-page PDF with `latexmk`.
- Checked the LaTeX log for fatal errors and overfull boxes.
- Rendered every PDF page to PNG and visually inspected the title page,
  theorem pages, reproduction appendix, references, and a full contact sheet.
- Ran PDF metadata, font embedding, and text-extraction checks.
- Produced an idempotent integration script, unified patch, construction
  diagram, manifest, and SHA-256 inventory.

## Not completed here

The container did not have `lean`, `lake`, or `elan`.  Runtime network access
was unavailable for installing the repository's pinned Lean 4.34.0 toolchain.
Therefore the following claims are **pending** rather than fabricated:

- successful Lean parsing and elaboration;
- kernel acceptance of every proof;
- exact `#print axioms` output;
- dependency-closure output from BusyLean's custom audit command;
- compliance with the 15-second definition and 60-second proof budgets;
- total clean-build timing on a reasonable machine.

## Acceptance criterion

The proposal should be called a verified BusyLean contender only after both
commands below succeed in a clean checkout at the recorded baseline:

```bash
python3 scripts/check.py
lake env lean test/Contender14Audit.lean
```

Until then, the accurate description is:

> a serious, fully specified, statically audited Lean proposal with compiled
> research documentation, awaiting its pinned kernel build.

## Risk assessment

The proof code is intentionally close to patterns already present in
`Comparison11.lean`, `Comparison13.lean`, and `MetaReflectionFacts.lean`.
The highest residual risks are ordinary elaboration details rather than a known
mathematical gap:

- definitional reduction in the theorem converting
  `iterateF13 42 contender_13` to `seed13 42 42`;
- implicit-argument inference around `operatorStage_progressive`;
- timing of recursive elaboration for the input-indexed transformer tower.

The integration notes explain conservative repairs if the pinned compiler
exposes any of these issues.  Such repairs should preserve all definitions and
mathematical statements.
