import BusyLean.MetaReflectionFacts

/-!
# Reflection lifted one level above transformers

`Transformer = Family → Family` is the level used by Contender 12.  This file
adds a total, structural hierarchy at the next level:

* a `MetaTransformer` maps transformers to transformers;
* `metaStage` iterates a meta-transformer along a well-founded `WTree Nat`;
* `rankLift schedule r` recursively promotes autonomous lifting through `r`
  meta-levels, using `schedule` at every positive level.

The proofs use only the explicit progressivity interface from
`BusyLean.MetaReflectionFacts`.  No monotonicity assumption is made.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- An operator on family transformers. -/
abbrev MetaTransformer := Transformer → Transformer

/-- A meta-transformer preserves the strict pointwise progressivity invariant. -/
def PreservesProgressive (amp : MetaTransformer) : Prop :=
  ∀ op, Progressive op → Progressive (amp op)

/-- Iterate a meta-transformer along a well-founded tree.

At a leaf, apply `amp` once.  At a node, recursively construct one transformer
from every child, splice that family of transformers, and apply `amp` to the
splice.  This is the exact next-type analogue of `operatorStage`.
-/
def metaStage (amp : MetaTransformer) (base : Transformer) :
    WTree Nat → Transformer
  | .leaf => amp base
  | .node f =>
      amp (spliceTransformers (fun i => metaStage amp base (f i)))

/-- Tree iteration of a progressivity-preserving meta-transformer remains
progressive. -/
theorem metaStage_progressive {amp : MetaTransformer}
    (hamp : PreservesProgressive amp) {base : Transformer}
    (hbase : Progressive base) :
    (a : WTree Nat) → Progressive (metaStage amp base a)
  | .leaf => hamp base hbase
  | .node f =>
      hamp
        (spliceTransformers (fun i => metaStage amp base (f i)))
        (spliceTransformers_progressive
          (fun i => metaStage_progressive hamp hbase (f i)))

/-- Branches used by one anchored rank promotion.

Coordinate zero preserves the preceding rank verbatim.  Every positive
coordinate carries the full schedule iteration.
-/
def rankBranches (schedule : WTree Nat) (amp : MetaTransformer)
    (base : Transformer) : Nat → Transformer
  | 0 => amp base
  | _ + 1 => metaStage amp base schedule

/-- Every anchored branch is progressive when the meta-transformer preserves
progressivity and the base is progressive. -/
theorem rankBranches_progressive (schedule : WTree Nat)
    {amp : MetaTransformer} (hamp : PreservesProgressive amp)
    {base : Transformer} (hbase : Progressive base) :
    ∀ i, Progressive (rankBranches schedule amp base i)
  | 0 => hamp base hbase
  | _ + 1 => metaStage_progressive hamp hbase schedule

/-- One anchored promotion of a meta-transformer.

The branch family is spliced and then autonomously lifted.  The final lift
makes the new rank strictly exceed the old rank at its canonical coordinate,
while retaining the schedule-driven amplification on positive coordinates.
-/
def rankStep (schedule : WTree Nat) (amp : MetaTransformer) :
    MetaTransformer :=
  fun base =>
    liftTransformer
      (spliceTransformers (rankBranches schedule amp base))

/-- Anchored promotion preserves progressivity. -/
theorem rankStep_preserves (schedule : WTree Nat) {amp : MetaTransformer}
    (hamp : PreservesProgressive amp) :
    PreservesProgressive (rankStep schedule amp) := by
  intro base hbase
  exact liftTransformer_progressive
    (spliceTransformers_progressive
      (rankBranches_progressive schedule hamp hbase))

/-- The rank hierarchy of meta-level autonomous lifting.

Rank zero is the autonomous lift from Contender 12.  Every successor is an
anchored promotion of the preceding meta-transformer.  The rank is a plain
natural number, so the hierarchy is executable in principle.
-/
def rankLift (schedule : WTree Nat) : Nat → MetaTransformer
  | 0 => liftTransformer
  | r + 1 => rankStep schedule (rankLift schedule r)

/-- Every finite rank preserves progressivity. -/
theorem rankLift_preserves (schedule : WTree Nat) :
    ∀ r, PreservesProgressive (rankLift schedule r)
  | 0 => fun base hbase => liftTransformer_progressive hbase
  | r + 1 =>
      rankStep_preserves schedule (rankLift_preserves schedule r)

/-- Convenient pointwise form of `rankLift_preserves`. -/
theorem rankLift_progressive (schedule : WTree Nat) (r : Nat)
    {base : Transformer} (hbase : Progressive base) :
    Progressive (rankLift schedule r base) :=
  rankLift_preserves schedule r base hbase

/-- Every successor rank strictly exceeds the preceding rank at canonical
coordinate zero.  This makes the rank parameter extensionally meaningful,
not merely a syntactic counter. -/
theorem rankLift_step_lt (schedule : WTree Nat) (r : Nat)
    {base : Transformer} (hbase : Progressive base) (seed : Family)
    {o n : Nat} :
    rankLift schedule r base seed 0 n <
      rankLift schedule (r + 1) base seed o n := by
  change
    rankBranches schedule (rankLift schedule r) base 0 seed 0 n <
      liftTransformer
        (spliceTransformers
          (rankBranches schedule (rankLift schedule r) base)) seed o n
  exact transformer_lt_lift_at
    (spliceTransformers_progressive
      (rankBranches_progressive schedule
        (rankLift_preserves schedule r) hbase))
    seed (Nat.zero_le n)

end BusyLean
