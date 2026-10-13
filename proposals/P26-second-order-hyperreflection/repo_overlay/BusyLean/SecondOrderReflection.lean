import BusyLean.HyperReflection

/-!
# Second-order diagonal hyperreflection

`HyperReflection` raises reflection from families to transformers and then to
transformer lifts. This module raises the construction one more type level.

A `HyperLift` maps transformer lifts to transformer lifts. The pointwise splice
`spliceLifts` makes a countable family of lifts dynamically selectable through
the output coordinate. `stageHyperLift` traverses a W-tree using an arbitrary
hyperlift. The base second-order operation `liftLift` applies a lift to its base
transformer and then closes the resulting transformer under the same lift along
the universal index. Finally, `diagonalHyperLift` repeats the diagonal pattern:
at successor rank, the preceding rank is used both as the local hyperlift and
as the first amplification of the base lift.

Every definition is structural and executable. There is no use of
`noncomputable`, `partial`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- A second-order lift acts on transformer lifts. -/
abbrev HyperLift := TransformerLift → TransformerLift

/-- Assemble countably many transformer lifts into one lift.

After a base transformer is supplied, output coordinate `i` selects lift `i`.
The selected transformer's canonical output coordinate is `0`, exactly as in
`spliceTransformers`. -/
def spliceLifts (ops : Nat → TransformerLift) : TransformerLift :=
  fun base => spliceTransformers (fun i => ops i base)

/-- Traverse a W-tree using an arbitrary hyperlift.

At a leaf, apply the hyperlift once. At a node, recursively construct one lift
for each child, splice those lifts, and apply the hyperlift to the splice. -/
def stageHyperLift (hyper : HyperLift) (base : TransformerLift) :
    WTree Nat → TransformerLift
  | .leaf => hyper base
  | .node f =>
      hyper (spliceLifts (fun i => stageHyperLift hyper base (f i)))

/-- The autonomous second-order lift.

For a lift `L` and a base transformer `T`, first form `L T`; then traverse the
universal index using `L` locally, with `L T` as the stage base. The occurrence
of `L` in both positions is the second-order analogue of the diagonal seed used
by `diagonalLift` at successor rank. -/
def liftLift (lift : TransformerLift) : TransformerLift :=
  fun base => stageLift lift (lift base) index

/-- A diagonal hierarchy of hyperlifts over a fixed schedule.

Rank zero is `liftLift`. At rank `k+1`, rank `k` is used both as the local
hyperlift at every node of the schedule and to pre-amplify the base lift. -/
def diagonalHyperLift (schedule : WTree Nat) : Nat → HyperLift
  | 0, base => liftLift base
  | k + 1, base =>
      stageHyperLift (diagonalHyperLift schedule k)
        (diagonalHyperLift schedule k base) schedule

end BusyLean
