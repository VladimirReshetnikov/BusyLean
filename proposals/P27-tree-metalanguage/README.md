# BusyLean Contender 35: transfinite metalanguage reflection

This package proposes a new closed Lean natural number:

```lean
def contender_35 : Nat := F35 (F35 42)
```

It is a verified successor to the current accepted Contender 34:

```lean
theorem contender_34_lt_contender_35 :
    contender_34 < contender_35
```

## Central idea

Contender 34 iterates a fixed first-order language-closure operator

```text
langLift : (CTree -> CTree) -> (CTree -> CTree)
```

along a countable tree ordinal.  Contender 35 raises the construction by one
functional type.  Its typed object language receives the previous
language-closure operator as a primitive:

```text
lift : (CTree -> CTree) -> CTree -> CTree
```

Programs can therefore construct tree transformers dynamically, pass them to a
lower-level whole-language closure, and continue computing with the resulting
trees.  The induced metalanguage closure is itself iterated along Contender
34's tree.  The resulting tree then feeds BusyLean's address-ladder reflection
and W-tree-ranked numerical lift.

This is intended as a qualitative hierarchy jump, not merely a larger numeric
parameter.  The article separates that structural argument from the exact
formal claim.  The exact formal claim is strict natural-number domination;
this package does not assert an unproved exact ordinal calibration.

## Verification

The exact Lean 4.34.0 project build passed on the isolated branch
`research/contender35-metalanguage-20261013`, commit
`f08df5f2a4cb21ec847d1fe3b9a95f7818a9e78e`, GitHub Actions run
`38440600428`.

With the accepted baseline precompiled, the three new modules built in 0.53 s,
0.33 s, and 0.33 s.  The dependency closure of `contender_35` contains 5,534
constants and avoids all thirty earlier contender constants.  The axiom audit
reports only the repository-permitted `propext` and `Quot.sound`; the new typed
interpreter uses no axioms.

See `VERIFICATION.md` and `verification/` for exact output.

## Package contents

- `article/contender35_metalanguage.tex` — comprehensive research article.
- `article/contender35_metalanguage.pdf` — compiled 25-page article.
- `BusyLean/Ordinal/TreeLanguage4.lean` — typed metalanguage and transfinite
  closure hierarchy.
- `BusyLean/Contender35.lean` — reflected family and closed number.
- `BusyLean/Comparison35.lean` — uniform bounds and final comparison theorem.
- `test/Contender35Audit.lean` — axiom and forbidden-dependency audit.
- `INTEGRATION.patch` — patch against BusyLean main at the stated baseline.
- `apply_to_checkout.sh` — idempotent installation helper.
- `BUILD.md` — build instructions.
- `THEOREM_INVENTORY.md` — declaration map.
- `VERIFICATION.md` — exact verification result.
- `verification/` — raw CI logs and workflow metadata.
- `MANIFEST.sha256` — integrity manifest generated last.

## Install and verify

```bash
./apply_to_checkout.sh /path/to/BusyLean
cd /path/to/BusyLean
lake build BusyLean.Ordinal.TreeLanguage4
lake build BusyLean.Contender35
lake build BusyLean.Comparison35
lake env lean test/Contender35Audit.lean
```

Alternatively, from the baseline checkout:

```bash
git apply /path/to/INTEGRATION.patch
```

## Do not evaluate the number

The term is computable in principle, but the represented natural is far beyond
feasible materialization.  Kernel-check definitions and proofs; do not run
`#eval BusyLean.contender_35` or force its full reduction.
