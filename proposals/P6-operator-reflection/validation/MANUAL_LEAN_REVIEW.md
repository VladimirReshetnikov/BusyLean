# Manual Lean source review

This note records the proof-engineering review performed without a local Lean
4.34.0 executable. It is not a substitute for kernel checking.

## Definition layer

### `runTransformer`

The recursion is structural on `WTree Nat`:

- leaf: return `op seed`;
- node `f`: recursively call `runTransformer op seed (f i)` only on immediate
  subtrees supplied by the constructor.

This follows the same accepted recursion pattern as the repository's existing
`stage` definition.

### `operatorStage`

The recursion is likewise structural on the outer `WTree Nat`. Recursive calls
occur only at `f i`, and the resulting transformer family is passed to
`spliceTransformers` before one autonomous lift.

### Constructivity

The definition modules contain none of the contest-excluded constructs. They do
not refer to the named constant `BusyLean.contender_6`; they reuse only its
underlying machinery (`reflectionTransformer`, `index`, and `p5Family`).

## Proof layer

### Compatibility lemma

`runTransformer_reflection_eq_stage` is a structural induction. At a node, both
sides reduce to `reflect` applied to extensionally equal families. The only
function equality is proved by `funext`, after which the induction hypothesis is
applied to child `f i`.

### Progressivity

`reflectionTransformer_progressive` is exactly
`oracle_lt_reflect`. `spliceTransformers_progressive` follows by selecting the
output-indexed child transformer. `liftTransformer_progressive` composes:

1. `seed i n < op seed i n`, and
2. `op seed i n < liftTransformer op seed o n`.

No oracle monotonicity is used.

### Explicit path into `index`

`transformer_lt_lift_at` uses the path

`leaf -> treesOfDepth 0 -> index`.

The first child is a leaf definitionally because `allTerms 0 = []`, `nthD`
returns `.zero`, and casting the numerical value of `.zero` to `WTree Nat`
returns the default leaf.

### Main comparison

`finalFamily_lt_autonomousFamily` repeats the same path at the outer operator
level. The outer leaf is `liftTransformer reflectionTransformer`, which the
compatibility lemma identifies with `stage p5Family index`, i.e. the complete
Contender-6 family. Specialization at input 42 yields
`contender_6_lt_contender_7`.

## Remaining authoritative check

Potential elaboration or termination-checker details can only be settled by
Lean. Run `python3 scripts/check_contender7.py` after applying the patch to the
recorded repository revision.
