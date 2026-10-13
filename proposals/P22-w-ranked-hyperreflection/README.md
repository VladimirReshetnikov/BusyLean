# BusyLean Contender 20: W-Ranked Diagonal Hyperreflection

This archive proposes a new closed computable natural number for the BusyLean
repository.  It replaces Contender 19's natural-number rank of diagonal
hyperreflection by an arbitrary well-founded `WTree Nat` rank.

The central definitions are:

```lean
def wDiagonalLift (schedule : WTree Nat) : WTree Nat -> TransformerLift
  | .leaf => liftTransformer
  | .node f =>
      let lower : TransformerLift :=
        spliceLifts (fun i => wDiagonalLift schedule (f i))
      fun base => stageLift lower (lower base) schedule

def family19 (n : Nat) : Nat := F19 (F19 n)

def F20 (n : Nat) : Nat :=
  wDiagonalLift (schedule20 n) (rank20 n)
    lTransformer (fun _ => family19) n n

def contender_20 : Nat := F20 (F20 42)
```

Lean proves:

```lean
theorem family19_lt_F20 (n : Nat) : family19 n < F20 n

theorem contender_19_lt_contender_20 :
  contender_19 < contender_20
```

## Validation status

The development was checked successfully on GitHub Actions at branch commit
`af98b262699f4d19712682fc9a0cffe2ed353217`, using Lean 4.34.0 and Lake 5.0.0.
With the accepted base through `Comparison19` precompiled:

- new definition phase: 0.84 s;
- new comparison proof phase: 0.35 s;
- focused axiom and dependency audit: success;
- `contender_20` closure: 4186 constants, avoiding all 15 earlier contender
  constants;
- reported axioms: only `propext` and inherited `Quot.sound`.

The exact machine-generated output is in `validation/validation-ci.log`.

## Archive layout

- `article/contender20_w_ranked.tex` - complete research article source.
- `article/contender20_w_ranked.pdf` - compiled and visually verified article.
- `lean/BusyLean/*.lean` - definition and theorem modules.
- `lean/test/Contender20Audit.lean` - focused axiom/dependency audit.
- `integration/0001-w-ranked-contender20.patch` - patch against BusyLean main at
  base commit `64d31a0cf6f1aa4477a088be5554957de6e87a61`.
- `integration/INTEGRATION.md` - installation and verification commands.
- `validation/CI_RECEIPT.md` and `validation/validation-ci.log` - reproducibility
  record.
- `figures/architecture.{dot,svg,pdf}` - editable construction diagram.
- `MANIFEST.sha256` - SHA-256 hashes for all packaged files.

## Mathematical status

The strict comparison with Contender 19 is formal and kernel-checked.  The
article's discussion of transfinite-rank strength is explicitly presented as a
structural/proof-theoretic interpretation, not as a proved identification with
one exact named ordinal or standard fast-growing hierarchy.

Do not evaluate `contender_20`.
