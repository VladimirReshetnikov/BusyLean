import BusyLean.HyperReflectionFacts

/-!
# W-rank hyperreflection

`diagonalLift` is indexed by a natural-number rank.  This module raises the
construction one type level.  A `HyperLift` transforms transformer lifts, and
`runHyperLift` iterates such an operation along a countably branching
well-founded `WTree Nat`.

The important proof invariant is `GoodLift`: a lift preserves progressive
transformers and is strictly inflationary.  No monotonicity in an oracle is
used.  The strict comparison follows an explicit child and an explicit splice
coordinate, exactly as in the first-order reflection proofs.

All definitions are structural and executable.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- One type level above `TransformerLift`. -/
abbrev HyperLift := TransformerLift → TransformerLift

/-- The two invariants needed to iterate a transformer lift safely. -/
abbrev GoodLift (lift : TransformerLift) : Prop :=
  PreservesProgressive lift ∧ StrictlyInflationary lift

/-- A hyperlift maps good lifts to good lifts. -/
abbrev PreservesGoodLift (op : HyperLift) : Prop :=
  ∀ lift, GoodLift lift → GoodLift (op lift)

/-- A hyperlift strictly exceeds its input lift at every visible coordinate. -/
abbrev StrictlyInflationary2 (op : HyperLift) : Prop :=
  ∀ (lift : TransformerLift), GoodLift lift →
    ∀ (base : Transformer), Progressive base →
      ∀ (seed : Family) (i o n : Nat), i ≤ n →
        lift base seed i n < op lift base seed o n

/-- Assemble a countable family of transformer lifts.  Output coordinate `i`
selects lift `i`; that lift is read at its canonical transformer coordinate
`0`, through `spliceTransformers`. -/
def spliceLifts (lifts : Nat → TransformerLift) : TransformerLift :=
  fun base => spliceTransformers (fun i => lifts i base)

/-- One rank step over a fixed schedule.  The input lift is used twice: first
to amplify the base and then as the local lift throughout the schedule. -/
def rankStep (schedule : WTree Nat) : HyperLift :=
  fun lift base => stageLift lift (lift base) schedule

/-- Iterate a hyperlift along a well-founded tree.

At a leaf, apply the hyperlift once.  At a node, recursively construct one lift
per child, splice those lifts, and apply the hyperlift to the splice. -/
def runHyperLift (op : HyperLift) (seed : TransformerLift) :
    WTree Nat → TransformerLift
  | .leaf => op seed
  | .node f =>
      op (spliceLifts (fun i => runHyperLift op seed (f i)))

/-- W-tree-indexed diagonal lifting over a fixed inner schedule. -/
def treeDiagonalLift (schedule rankTree : WTree Nat)
    (seed : TransformerLift) : TransformerLift :=
  runHyperLift (rankStep schedule) seed rankTree

/-- Splicing preserves the progressive-preservation invariant. -/
theorem spliceLifts_preservesProgressive {lifts : Nat → TransformerLift}
    (hlifts : ∀ i, PreservesProgressive (lifts i)) :
    PreservesProgressive (spliceLifts lifts) := by
  intro base hbase
  exact spliceTransformers_progressive (fun i => hlifts i base hbase)

/-- Splicing preserves strict inflationarity. -/
theorem spliceLifts_strictlyInflationary {lifts : Nat → TransformerLift}
    (hlifts : ∀ i, StrictlyInflationary (lifts i)) :
    StrictlyInflationary (spliceLifts lifts) := by
  intro base hbase seed i o n hi
  change base seed i n < lifts o base seed 0 n
  exact hlifts o base hbase seed i 0 n hi

/-- A splice of good lifts is good. -/
theorem spliceLifts_good {lifts : Nat → TransformerLift}
    (hlifts : ∀ i, GoodLift (lifts i)) :
    GoodLift (spliceLifts lifts) :=
  ⟨spliceLifts_preservesProgressive (fun i => (hlifts i).1),
    spliceLifts_strictlyInflationary (fun i => (hlifts i).2)⟩

/-- One rank step maps good lifts to good lifts. -/
theorem rankStep_preservesGood (schedule : WTree Nat) :
    PreservesGoodLift (rankStep schedule) := by
  intro lift hlift
  rcases hlift with ⟨hpres, hstrict⟩
  constructor
  · intro base hbase
    change Progressive (stageLift lift (lift base) schedule)
    exact stageLift_progressive lift hpres
      (lift base) (hpres base hbase) schedule
  · intro base hbase seed i o n hi
    change base seed i n <
      stageLift lift (lift base) schedule seed o n
    have hfirst : base seed i n < lift base seed i n :=
      hstrict base hbase seed i i n hi
    have hsecond : lift base seed i n <
        stageLift lift (lift base) schedule seed o n :=
      base_lt_stageLift lift hpres hstrict
        (lift base) (hpres base hbase) schedule seed i o n hi
    exact Nat.lt_trans hfirst hsecond

/-- One rank step is strictly inflationary at the level of lifts. -/
theorem rankStep_strictlyInflationary2 (schedule : WTree Nat) :
    StrictlyInflationary2 (rankStep schedule) := by
  intro lift hlift base hbase seed i o n hi
  rcases hlift with ⟨hpres, hstrict⟩
  change lift base seed i n <
    stageLift lift (lift base) schedule seed o n
  exact base_lt_stageLift lift hpres hstrict
    (lift base) (hpres base hbase) schedule seed i o n hi

/-- W-tree iteration preserves goodness. -/
theorem runHyperLift_good (op : HyperLift)
    (hop : PreservesGoodLift op)
    (seed : TransformerLift) (hseed : GoodLift seed) :
    (a : WTree Nat) → GoodLift (runHyperLift op seed a)
  | .leaf => hop seed hseed
  | .node f =>
      hop
        (spliceLifts (fun i => runHyperLift op seed (f i)))
        (spliceLifts_good
          (fun i => runHyperLift_good op hop seed hseed (f i)))

/-- Every W-tree stage strictly exceeds its seed lift.

The node case follows child zero, identifies it with coordinate zero of the
splice, and then applies strictness of the hyperlift. -/
theorem seed_lt_runHyperLift (op : HyperLift)
    (hpres : PreservesGoodLift op)
    (hstrict : StrictlyInflationary2 op)
    (seedLift : TransformerLift) (hseed : GoodLift seedLift) :
    (a : WTree Nat) →
      ∀ (base : Transformer), Progressive base →
        ∀ (seed : Family) (i o n : Nat), i ≤ n →
          seedLift base seed i n <
            runHyperLift op seedLift a base seed o n
  | .leaf, base, hbase, seed, i, o, n, hi =>
      hstrict seedLift hseed base hbase seed i o n hi
  | .node f, base, hbase, seed, i, o, n, hi => by
      have hchild :
          seedLift base seed i n <
            runHyperLift op seedLift (f 0) base seed 0 n :=
        seed_lt_runHyperLift op hpres hstrict seedLift hseed
          (f 0) base hbase seed i 0 n hi
      have hsplice : GoodLift
          (spliceLifts (fun j => runHyperLift op seedLift (f j))) :=
        spliceLifts_good
          (fun j => runHyperLift_good op hpres seedLift hseed (f j))
      have hparent := hstrict
        (spliceLifts (fun j => runHyperLift op seedLift (f j)))
        hsplice base hbase seed 0 o n (Nat.zero_le n)
      change
        runHyperLift op seedLift (f 0) base seed 0 n <
          runHyperLift op seedLift (.node f) base seed o n at hparent
      exact Nat.lt_trans hchild hparent

/-- The W-rank diagonal lift is good whenever its seed lift is good. -/
theorem treeDiagonalLift_good (schedule rankTree : WTree Nat)
    (seed : TransformerLift) (hseed : GoodLift seed) :
    GoodLift (treeDiagonalLift schedule rankTree seed) := by
  simpa [treeDiagonalLift] using
    runHyperLift_good (rankStep schedule)
      (rankStep_preservesGood schedule) seed hseed rankTree

/-- The W-rank diagonal lift strictly exceeds its seed lift. -/
theorem seed_lt_treeDiagonalLift (schedule rankTree : WTree Nat)
    (seedLift : TransformerLift) (hseed : GoodLift seedLift)
    (base : Transformer) (hbase : Progressive base)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    seedLift base seed i n <
      treeDiagonalLift schedule rankTree seedLift base seed o n := by
  simpa [treeDiagonalLift] using
    seed_lt_runHyperLift (rankStep schedule)
      (rankStep_preservesGood schedule)
      (rankStep_strictlyInflationary2 schedule)
      seedLift hseed rankTree base hbase seed i o n hi

end BusyLean
