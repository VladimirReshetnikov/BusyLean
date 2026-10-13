import BusyLean.MetaReflection

/-!
# Diagonal hyperreflection

`operatorStage` lifts one progressive transformer through a W-tree.  This
module abstracts that recursion over an arbitrary lifting operation and then
diagonalizes it.  At rank zero we use the repository's autonomous
`liftTransformer`.  At successor rank, the preceding rank is used both

* as the local lifting operation at every node of a schedule, and
* to pre-amplify the base transformer before that schedule is traversed.

Thus every successor rank contains the preceding rank twice: extensionally as
an operator and intensionally in its seed.  All definitions are structural and
computable.

Adopted unchanged from proposal P17 (`proposals/P17-diagonal-hyperreflection`,
"Diagonal hyperreflection"); the same idea appears independently in P20.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- A lift acts on transformers rather than directly on oracle families. -/
abbrev TransformerLift := Transformer → Transformer

/-- Traverse a W-tree using an arbitrary transformer lift.

At a leaf, apply `lift` to the base transformer.  At a node, recursively build
one transformer for each child, splice those transformers into a single
transformer, and apply `lift` to the splice.  Existing `operatorStage` is the
special case `stageLift liftTransformer`.
-/
def stageLift (lift : TransformerLift) (base : Transformer) :
    WTree Nat → Transformer
  | .leaf => lift base
  | .node f =>
      lift (spliceTransformers (fun i => stageLift lift base (f i)))

/-- The diagonal hierarchy of transformer lifts over a fixed schedule.

Rank zero is ordinary autonomous lifting.  At rank `k+1`, rank `k` is used as
both the lift and the first amplification of the base.  This is substantially
stronger than merely repeating a fixed operator-stage map.
-/
def diagonalLift (schedule : WTree Nat) : Nat → TransformerLift
  | 0, base => liftTransformer base
  | k + 1, base =>
      stageLift (diagonalLift schedule k)
        (diagonalLift schedule k base) schedule

end BusyLean
