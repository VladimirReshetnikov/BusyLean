# BusyLean Contender 20 research package

## Proposal

**Contender 20: Third-Order Autonomous Hyperreflection**

This package targets the audited BusyLean `main` commit
`64d31a0cf6f1aa4477a088be5554957de6e87a61`, whose accepted entry is
Contender 19.  The new construction raises the repository's reflection
machinery one complete type level:

```lean
abbrev LiftTransformer := TransformerLift → TransformerLift

def contender_20 : Nat := F20 (F20 42)
```

The initial lift is a self-ranked instance of the accepted `diagonalLift`.
`superIterate` then reflects over whole transformer lifts along a self-sized
autonomous W-tree.  Applying the resulting lift to large-Veblen reflection
produces a countable family, and `F20` performs one final large-Veblen
reflection over that entire family.

The intended kernel-checked comparison is:

```lean
theorem contender_19_lt_contender_20 : contender_19 < contender_20
```

The stronger architectural theorem is:

```lean
theorem diagonalLift_lt_lift20 ... :
  diagonalLift (schedule20 n) (innerRank20 n) base seed i n <
    lift20 n base seed o n
```

Thus the construction is not merely a reseeding or one extra numeric
iteration.  It strictly dominates a complete current-style diagonal hyperlift
at every visible coordinate, before the final object-language reflection is
performed.

## Contents

- `article/contender20.tex` and `article/contender20.pdf`: research article.
- `overlay/BusyLean/SuperReflection.lean`: third-order definitions.
- `overlay/BusyLean/SuperReflectionFacts.lean`: invariant and growth proofs.
- `overlay/BusyLean/Contender20.lean`: the proposed family and closed number.
- `overlay/BusyLean/Comparison20.lean`: comparison and program bounds.
- `overlay/test/Audit20.lean`: axiom and transitive-dependency audit.
- `overlay/scripts/check20.py`: clean-build budget and audit harness.
- `install.sh`: guarded overlay installer.
- `busylean-contender20.patch`: equivalent unified patch.
- `artifacts/`: static audit, claim matrix, diagrams, and design notes.
- `source_audit/baseline.json`: audited commit and source blob provenance.
- `MANIFEST.sha256`: package integrity ledger.

## Install and validate

```bash
unzip BusyLean_Contender20_ThirdOrder_Hyperreflection.zip
cd BusyLean_Contender20_ThirdOrder_Hyperreflection
./install.sh /path/to/BusyLean
cd /path/to/BusyLean
python3 scripts/check20.py
```

The installer refuses to overwrite proposal files unless `--force` is given.
It checks the pinned toolchain string, warns on a different Git commit, copies
the overlay, and adds the four new imports to `BusyLean.lean`.

## Validation status

The source-level static audit passes; the article compiles; every PDF page was
rendered and inspected.  The execution environment used to build this package
did not contain Lean or Lake, so the package **does not claim kernel replay,
axiom closure, or timing-budget validation**.  `scripts/check20.py` is the
required final acceptance step in a checkout with Lean 4.34.0.

See `BUILD_STATUS.md` and `artifacts/claim_matrix.csv` for the precise division
between verified evidence and pending kernel checks.
