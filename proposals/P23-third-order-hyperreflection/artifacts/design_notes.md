# Design notes: why this is not merely Contender 19 plus one

The accepted `diagonalLift` has type

```text
WTree Nat -> Nat -> (Transformer -> Transformer)
```

and therefore constructs a natural hierarchy of **transformer lifts**.  The new
module abstracts the next type level:

```text
LiftTransformer = TransformerLift -> TransformerLift
```

Its central operation, `liftStage`, branches over and splices whole transformer
lifts before applying a lift transformer.  The local operation `promoteLift`
encapsulates one complete successor of the accepted `diagonalLift` hierarchy.
`superClosure` then iterates `promoteLift` along an autonomous W-tree, and
`superIterate` repeats that closure through a previous-number-controlled finite
meta-rank.

The proof architecture deliberately avoids oracle monotonicity.  The invariant
`GoodLift` packages the two properties that are actually available:

1. preservation of progressive transformers; and
2. strict inflationarity on progressive transformers.

At a `liftStage` node the proof follows child zero, identifies it with
coordinate zero of `spliceLifts`, and applies strictness at the parent.  This is
the same explicit-occurrence discipline that made the accepted reflection
proofs robust, raised one full type level.

The final construction adds another meaningful layer: the third-order lift
produces a countable family, and `F20 n` performs large-Veblen reflection over
that entire family.  Consequently the theorem `final_lvalue_lt_F20` concerns
programs run relative to the final packed family rather than merely the old
seed.
