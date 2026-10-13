# BusyLean Contender 11: self-indexed forest reflection

This archive proposes a new constructive BusyLean entry on top of repository
commit `4c4b03d0e2003c479e3bee90a21c8bea13f66c40`.

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)
def F11 (n : Nat) : Nat := stage11 (fun _ => family10) index n
def contender_11 : Nat := F11 (F11 42)

theorem contender_10_lt_contender_11 :
    contender_10 < contender_11
```

`stage11` performs kind-polymorphic System F-omega reflection at every node of
BusyLean's self-indexed W-tree.  Each node receives the stages of its children
as a dynamically addressable oracle family, encoded through the repository's
existing `packFamily`.  The seed is Contender 10's *generating construction*
`n ↦ F10 (F10 n)`, never the constant `contender_10`.

The formal result is stronger than the terminal inequality:

- `family10_lt_F11`: pointwise domination of the entire Contender 10 family;
- `fvalue_lt_contender_11`: domination of every enumerated kind-polymorphic
  program at the final inner budget and root forest oracle;
- `defined_tree_eventually_lt11`: eventual domination along every W-language
  definable index tree.

## Verification status

A reconstructed verification unit containing the exact 30-module dependency
closure of `BusyLean.Comparison10` plus the two supplied modules was checked by
AXLE under Lean 4.34.0.  The recorded proof run returned `okay = true`, an empty
`failed_declarations` list, and total request time 8,900 ms.  All five audited
declarations reported exactly the permitted axioms `propext` and `Quot.sound`.
A separate closure audit reported 1,460 reachable constants and no occurrence
of any forbidden predecessor constant.

This is an independent merged-source check, not an official staged Lake build.
After integration, run `python3 scripts/check_contender11.py` in the BusyLean
repository to enforce the contest's 15-second definition and 60-second proof
budgets on the target machine.  Never evaluate any contender.

## Archive layout

- `BusyLean/Contender11.lean` - definitions;
- `BusyLean/Comparison11.lean` - comparisons and domination theorems;
- `test/Contender11Audit.lean` - axiom and dependency audit;
- `scripts/check_contender11.py` - staged local Lake build and audit;
- `scripts/verify_axle.py` - reproducible independent merged-source check;
- `article/contender11.tex` and `.pdf` - detailed research article;
- `integration/INTEGRATION.md` - integration instructions;
- `patches/0001-contender11.patch` - patch against the pinned snapshot;
- `verification/` - recorded verification receipt and source hashes;
- `MANIFEST.sha256` - archive integrity manifest.

## Mathematical caution

The strict inequalities and universal bounded-program statements are formal.
Any fast-growing-hierarchy or proof-theoretic calibration in the article is
explicitly heuristic: BusyLean does not formalize an ordinal analysis of the
kind-polymorphic language.

## License

The supplied code and documentation are distributed under the repository's
MIT No Attribution License; see `LICENSE`.
