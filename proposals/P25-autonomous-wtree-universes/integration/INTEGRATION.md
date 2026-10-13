# Integration guide

## Validated target

Apply the code to BusyLean base revision:

```text
64d31a0cf6f1aa4477a088be5554957de6e87a61
```

The exact validated branch head is:

```text
fd43cae755356719c907fde0b0b131d258a30e18
```

## Option 1: use the research branch

The seven repository additions are already available on:

```text
research/contender20-autonomous-wtree-ladder
```

Review the branch, run the validator, and merge or cherry-pick under the
repository's normal policy.

## Option 2: apply the bundled patch

From a clean checkout at the base revision:

```bash
git apply integration/contender20.patch
python3 scripts/check_contender20.py
```

The patch adds only new files; it does not edit the existing README, umbrella
imports, or the main audit.

## Added files

```text
.github/workflows/contender20-check.yml
BusyLean/Ordinal/WTreeLadder.lean
BusyLean/Contender20.lean
BusyLean/Comparison20.lean
scripts/check_contender20.py
test/WTreeLadderSmoke.lean
test/Contender20Audit.lean
```

## Suggested post-review integration edits

After the proposal is accepted:

1. Import `BusyLean.Comparison20` from whichever umbrella module the project
   uses for the current comparison chain.
2. Extend `test/Audit.lean` with the new number, comparison, orbit, language,
   and well-foundedness declarations.
3. Update `scripts/check.py` so the previous target is `BusyLean.Comparison19`
   and the new definition/proof targets are `BusyLean.Contender20` and
   `BusyLean.Comparison20`.
4. Add a new top section to `README.md` describing the autonomous W-tree
   ladder and the exact comparison theorem.
5. Decide whether the 20-page article belongs under `docs/`, `proposals/`, or
   another repository documentation directory.

Those edits were intentionally not made on the research branch so the proposal
can be reviewed without displacing Contender 19 on `main`.

## Validation

```bash
python3 scripts/check_contender20.py
```

Expected incremental times from the recorded GitHub Actions run were 0.746 s
for definitions and 0.454 s for proofs, comfortably below the 15 s and 60 s
budgets. Wall-clock times will vary by machine.
