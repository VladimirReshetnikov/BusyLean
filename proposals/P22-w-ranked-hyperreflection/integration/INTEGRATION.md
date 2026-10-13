# Integration into BusyLean

## Audited base

The patch was prepared against BusyLean main commit:

`64d31a0cf6f1aa4477a088be5554957de6e87a61`

The validated research branch commit is:

`af98b262699f4d19712682fc9a0cffe2ed353217`

Research branch:

`research/w-ranked-contender20-20261013`

## Apply the patch

From the root of a BusyLean checkout at the audited base:

```bash
git apply --check /path/to/0001-w-ranked-contender20.patch
git apply /path/to/0001-w-ranked-contender20.patch
```

The patch adds:

- `BusyLean/TreeHyperReflection.lean`
- `BusyLean/TreeHyperReflectionFacts.lean`
- `BusyLean/Contender20.lean`
- `BusyLean/Comparison20.lean`
- `test/Contender20Audit.lean`

and appends the corresponding imports to `BusyLean.lean`.

## Build and audit

```bash
lake build BusyLean.Comparison19
lake build BusyLean.Contender20
lake build BusyLean.Comparison20
lake env lean test/Contender20Audit.lean
```

A full project build can then be run with:

```bash
lake build
```

## Expected focused-audit conclusions

- `BusyLean.contender_19_lt_contender_20` typechecks.
- `BusyLean.contender_20` depends only on `propext` and `Quot.sound`.
- Its transitive constant closure avoids `BusyLean.contender_5` through
  `BusyLean.contender_19`.
- The generic W-ranked growth theorems depend only on `propext`.

## Optional standard-audit merge

The focused audit is deliberately separate so the overlay is easy to review.
For permanent repository integration, its `#print axioms`, closure assertion,
and `#check` declarations can also be copied into `test/Audit.lean`.

## Article build

From `article/`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error contender20_w_ranked.tex
```

The article expects `../figures/architecture.pdf`.
