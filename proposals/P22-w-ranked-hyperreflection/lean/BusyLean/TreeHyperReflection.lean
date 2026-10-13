import BusyLean.HyperReflection

/-!
# W-ranked diagonal hyperreflection

`diagonalLift schedule k` is indexed by a natural-number rank.  This module
replaces that finite rank by an arbitrary well-founded `WTree Nat`.

At a leaf we use the ordinary autonomous lift.  At a node, all immediate
sub-ranks are assembled into a single lift by `spliceLifts`.  That lower-rank
lift is then used twice, exactly as in one successor step of finite diagonal
hyperreflection:

* it pre-amplifies the base transformer; and
* it is the local lifting operation at every node of the fixed schedule.

The definition is structural recursion on the rank tree.  It is executable and
uses no noncomputable features or axioms.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Assemble a countable family of transformer lifts into one lift.

For an output coordinate `i`, the resulting transformed operator selects lift
`i` and uses that transformer's canonical output coordinate `0`.  This is the
lift-level analogue of `spliceTransformers`.
-/
def spliceLifts (lifts : Nat → TransformerLift) : TransformerLift :=
  fun base => spliceTransformers (fun i => lifts i base)

/-- Diagonal hyperreflection indexed by an arbitrary well-founded rank tree.

A leaf is rank zero.  At a node, the family of all child-rank lifts is spliced
into one lift `lower`; the parent then performs a full `stageLift` with `lower`,
after first applying `lower` to the base.  Thus every child rank occurs both in
the local operator family and in the pre-amplified seed.
-/
def wDiagonalLift (schedule : WTree Nat) : WTree Nat → TransformerLift
  | .leaf => liftTransformer
  | .node f =>
      let lower : TransformerLift :=
        spliceLifts (fun i => wDiagonalLift schedule (f i))
      fun base => stageLift lower (lower base) schedule

end BusyLean
