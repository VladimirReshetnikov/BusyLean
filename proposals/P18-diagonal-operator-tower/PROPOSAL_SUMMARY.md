# Contender 14: self-indexed diagonal operator reflection

## Definition

The proposed number is

```lean
def contender_14 : Nat := F14 (F14 42)
```

where `F14 n` is produced by a tower of operator-stage closures of height

```lean
def family13 (n : Nat) : Nat := F13 (F13 n)
```

and hence the tower height at input 42 is definitionally Contender 13. The new
executable definition uses `F13` as a construction, but does not mention the
closed constant `contender_13`.

The base transformer reflects the repository's dynamic-kind System F-omega
language against a packed countable oracle family. An explicit prefix maximum
makes it progressive without assuming oracle monotonicity, which is false in
general for oracle programs that can branch on returned values.

Each successor tower rank applies the generic `operatorStage` construction to
the entire previous transformer. The rank-dependent schedule has:

- a leaf at branch zero, used as an explicit strict-comparison witness; and
- countably many branches carrying increasing `Autonomous.hyper` schedules
  above `tree12`.

## Supplied theorem chain

The comparison module is designed to prove:

- `fdFamilyTransformer_progressive`;
- `diagonalOperatorTower_progressive` for every finite rank;
- `diagonalOperatorTower_step_lt`, a strict pointwise increase at each
  successor rank;
- `diagonalOperatorTower_rank_lt`, strict comparison of arbitrary lower and
  higher ranks;
- `family13_lt_F14` and `input_lt_F14`;
- `fvalue_lt_F14`, domination of every bounded dynamic-kind program evaluated
  with the packed predecessor-family oracle;
- `contender_13_lt_contender_14` and therefore domination of all earlier
  accepted contenders.

## Why the increase is structural

The proposal is not merely `F13` applied one more time. It combines three
amplifiers:

1. family-aware reflection over the strongest certified object language in the
   baseline;
2. operator-level reflection, where each new rank closes over the complete
   previous transformer; and
3. a self-indexed rank equal, at input 42, to the full predecessor number.

The strict rank theorems give an internal chain of explicit inequalities across
that predecessor-sized tower. No exact fast-growing or proof-theoretic ordinal
calibration is claimed without a separate analysis.
