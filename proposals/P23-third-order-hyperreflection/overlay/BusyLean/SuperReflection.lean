import BusyLean.HyperReflection

/-!
# Third-order autonomous hyperreflection

The accepted hyperreflection layer acts on `Transformer`s through
`TransformerLift = Transformer → Transformer`.  This module raises the
construction one more type level.

A `LiftTransformer` maps transformer lifts to transformer lifts.  We can splice
a countable family of lifts coordinatewise, promote a lift by one ordinary
hyperreflection step, iterate an arbitrary lift transformer along a W-tree, and
then iterate that whole autonomous closure through a finite meta-rank.

Every definition is structural recursion on `Nat` or `WTree Nat`.  There is no
partiality, oracle, or evaluation-time metaprogramming.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- One type level above `TransformerLift`. -/
abbrev LiftTransformer := TransformerLift → TransformerLift

/-- Splice a countable family of transformer lifts.

Output coordinate `i` selects lift `i`; the selected transformer uses its
canonical output coordinate `0`, exactly as `spliceTransformers` does one level
below.
-/
def spliceLifts (lifts : Nat → TransformerLift) : TransformerLift :=
  fun base => spliceTransformers (fun i => lifts i base)

/-- Promote a transformer lift by one schedule-driven hyperreflection step.

This abstracts the successor clause of `diagonalLift`: the incoming lift is
used both to amplify the base transformer and as the local lifting operation
at every node of the schedule.
-/
def promoteLift (schedule : WTree Nat) : LiftTransformer :=
  fun lift base => stageLift lift (lift base) schedule

/-- Iterate a lift transformer along a well-founded tree.

This is the exact next-type analogue of `stageLift`.
-/
def liftStage (amp : LiftTransformer) (base : TransformerLift) :
    WTree Nat → TransformerLift
  | .leaf => amp base
  | .node f =>
      amp (spliceLifts (fun i => liftStage amp base (f i)))

/-- One autonomous third-order closure.

The same schedule is used internally by `promoteLift` and externally by
`liftStage`.  Thus the schedule controls both the local hyperreflection and the
branching reflection over whole lifts.
-/
def superClosure (schedule : WTree Nat) (base : TransformerLift) :
    TransformerLift :=
  liftStage (promoteLift schedule) base schedule

/-- Iterate the third-order closure through a finite meta-rank. -/
def superIterate (schedule : WTree Nat) :
    Nat → TransformerLift → TransformerLift
  | 0, base => base
  | k + 1, base => superClosure schedule (superIterate schedule k base)

end BusyLean
