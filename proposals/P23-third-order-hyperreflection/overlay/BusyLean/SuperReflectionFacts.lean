import BusyLean.SuperReflection
import BusyLean.HyperReflectionFacts

/-!
# Growth facts for third-order autonomous hyperreflection

The crucial invariant is `GoodLift`: a transformer lift preserves progressive
transformers and is strictly inflationary on every progressive transformer.
The proofs below never assume semantic monotonicity in an oracle family.  Such
monotonicity is false for reflective object languages because programs may
branch on oracle values.  Instead every inequality follows an explicit visible
coordinate or the explicit zero child of a tree node.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- A lift has both properties needed by the higher construction. -/
def GoodLift (lift : TransformerLift) : Prop :=
  PreservesProgressive lift ∧ StrictlyInflationary lift

/-- A lift transformer maps good lifts to good lifts. -/
def PreservesGoodLifts (amp : LiftTransformer) : Prop :=
  ∀ lift, GoodLift lift → GoodLift (amp lift)

/-- A lift transformer strictly exceeds its input lift on every progressive
base transformer and every visible coordinate. -/
def LiftStrictlyInflationary (amp : LiftTransformer) : Prop :=
  ∀ lift, GoodLift lift →
    ∀ (base : Transformer), Progressive base →
    ∀ (seed : Family) (i o n : Nat), i ≤ n →
      lift base seed i n < amp lift base seed o n

/-- Coordinatewise splicing preserves the good-lift invariant. -/
theorem spliceLifts_good (lifts : Nat → TransformerLift)
    (hlifts : ∀ i, GoodLift (lifts i)) :
    GoodLift (spliceLifts lifts) := by
  constructor
  · intro base hbase
    exact spliceTransformers_progressive
      (fun i => (hlifts i).1 base hbase)
  · intro base hbase seed i o n hi
    change base seed i n < lifts o base seed 0 n
    exact (hlifts o).2 base hbase seed i 0 n hi

/-- Promotion maps every good lift to another good lift. -/
theorem promoteLift_good (schedule : WTree Nat) (lift : TransformerLift)
    (hlift : GoodLift lift) :
    GoodLift (promoteLift schedule lift) := by
  constructor
  · intro base hbase
    exact stageLift_progressive lift hlift.1
      (lift base) (hlift.1 base hbase) schedule
  · intro base hbase seed i o n hi
    have hfirst : base seed i n < lift base seed i n :=
      hlift.2 base hbase seed i i n hi
    have hsecond :
        lift base seed i n <
          stageLift lift (lift base) schedule seed o n :=
      base_lt_stageLift lift hlift.1 hlift.2
        (lift base) (hlift.1 base hbase)
        schedule seed i o n hi
    exact Nat.lt_trans hfirst hsecond

/-- Promotion preserves good lifts. -/
theorem promoteLift_preservesGood (schedule : WTree Nat) :
    PreservesGoodLifts (promoteLift schedule) :=
  fun lift hlift => promoteLift_good schedule lift hlift

/-- Promotion strictly exceeds the promoted lift itself. -/
theorem lift_lt_promoteLift (schedule : WTree Nat)
    (lift : TransformerLift) (hlift : GoodLift lift)
    (base : Transformer) (hbase : Progressive base)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    lift base seed i n < promoteLift schedule lift base seed o n :=
  base_lt_stageLift lift hlift.1 hlift.2
    (lift base) (hlift.1 base hbase)
    schedule seed i o n hi

/-- Promotion is strictly inflationary at the lift level. -/
theorem promoteLift_liftStrict (schedule : WTree Nat) :
    LiftStrictlyInflationary (promoteLift schedule) :=
  fun lift hlift base hbase seed i o n hi =>
    lift_lt_promoteLift schedule lift hlift base hbase seed i o n hi

/-- Tree iteration preserves the good-lift invariant. -/
theorem liftStage_good (amp : LiftTransformer)
    (hamp : PreservesGoodLifts amp)
    (baseLift : TransformerLift) (hbaseLift : GoodLift baseLift) :
    (a : WTree Nat) → GoodLift (liftStage amp baseLift a)
  | .leaf => hamp baseLift hbaseLift
  | .node f => by
      apply hamp
      exact spliceLifts_good
        (fun i => liftStage amp baseLift (f i))
        (fun i => liftStage_good amp hamp baseLift hbaseLift (f i))

/-- If the local lift transformer is strict, every tree stage strictly exceeds
its original base lift.

The node case follows child zero explicitly, identifies it with coordinate zero
of the splice, and then applies strictness at the parent. -/
theorem baseLift_lt_liftStage (amp : LiftTransformer)
    (hpres : PreservesGoodLifts amp)
    (hstrict : LiftStrictlyInflationary amp)
    (baseLift : TransformerLift) (hbaseLift : GoodLift baseLift) :
    (a : WTree Nat) →
      ∀ (base : Transformer), Progressive base →
      ∀ (seed : Family) (i o n : Nat), i ≤ n →
        baseLift base seed i n < liftStage amp baseLift a base seed o n
  | .leaf, base, hbase, seed, i, o, n, hi =>
      hstrict baseLift hbaseLift base hbase seed i o n hi
  | .node f, base, hbase, seed, i, o, n, hi => by
      have hchild :
          baseLift base seed i n <
            liftStage amp baseLift (f 0) base seed 0 n :=
        baseLift_lt_liftStage amp hpres hstrict baseLift hbaseLift
          (f 0) base hbase seed i 0 n hi
      have hchildren :
          ∀ j, GoodLift (liftStage amp baseLift (f j)) :=
        fun j => liftStage_good amp hpres baseLift hbaseLift (f j)
      have hsplice :
          GoodLift (spliceLifts (fun j => liftStage amp baseLift (f j))) :=
        spliceLifts_good
          (fun j => liftStage amp baseLift (f j)) hchildren
      have hparent :
          liftStage amp baseLift (f 0) base seed 0 n <
            liftStage amp baseLift (.node f) base seed o n := by
        change
          spliceLifts (fun j => liftStage amp baseLift (f j))
              base seed 0 n <
            amp (spliceLifts (fun j => liftStage amp baseLift (f j)))
              base seed o n
        exact hstrict
          (spliceLifts (fun j => liftStage amp baseLift (f j)))
          hsplice base hbase seed 0 o n (Nat.zero_le n)
      exact Nat.lt_trans hchild hparent

/-- One autonomous third-order closure preserves the good-lift invariant. -/
theorem superClosure_good (schedule : WTree Nat)
    (lift : TransformerLift) (hlift : GoodLift lift) :
    GoodLift (superClosure schedule lift) :=
  liftStage_good (promoteLift schedule)
    (promoteLift_preservesGood schedule) lift hlift schedule

/-- One autonomous third-order closure strictly exceeds its input lift. -/
theorem lift_lt_superClosure (schedule : WTree Nat)
    (lift : TransformerLift) (hlift : GoodLift lift)
    (base : Transformer) (hbase : Progressive base)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    lift base seed i n < superClosure schedule lift base seed o n :=
  baseLift_lt_liftStage (promoteLift schedule)
    (promoteLift_preservesGood schedule)
    (promoteLift_liftStrict schedule)
    lift hlift schedule base hbase seed i o n hi

/-- Every finite meta-rank is a good lift. -/
theorem superIterate_good (schedule : WTree Nat)
    (initial : TransformerLift) (hinitial : GoodLift initial) :
    ∀ k, GoodLift (superIterate schedule k initial)
  | 0 => hinitial
  | k + 1 =>
      superClosure_good schedule
        (superIterate schedule k initial)
        (superIterate_good schedule initial hinitial k)

/-- Convenient progressivity projection for a finite meta-rank. -/
theorem superIterate_preservesProgressive (schedule : WTree Nat)
    (initial : TransformerLift) (hinitial : GoodLift initial) (k : Nat) :
    PreservesProgressive (superIterate schedule k initial) :=
  (superIterate_good schedule initial hinitial k).1

/-- Convenient strictness projection for a finite meta-rank. -/
theorem superIterate_strictlyInflationary (schedule : WTree Nat)
    (initial : TransformerLift) (hinitial : GoodLift initial) (k : Nat) :
    StrictlyInflationary (superIterate schedule k initial) :=
  (superIterate_good schedule initial hinitial k).2

/-- The meta-rank hierarchy is strictly increasing at every successor. -/
theorem superIterate_step_lt (schedule : WTree Nat) (k : Nat)
    (initial : TransformerLift) (hinitial : GoodLift initial)
    (base : Transformer) (hbase : Progressive base)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    superIterate schedule k initial base seed i n <
      superIterate schedule (k + 1) initial base seed o n := by
  simpa [superIterate] using
    (lift_lt_superClosure schedule
      (superIterate schedule k initial)
      (superIterate_good schedule initial hinitial k)
      base hbase seed i o n hi)

/-- Every positive meta-rank strictly exceeds the initial lift. -/
theorem lift_lt_superIterate_succ (schedule : WTree Nat)
    (initial : TransformerLift) (hinitial : GoodLift initial) :
    ∀ (k : Nat) (base : Transformer), Progressive base →
      ∀ (seed : Family) (i o n : Nat), i ≤ n →
        initial base seed i n <
          superIterate schedule (k + 1) initial base seed o n
  | 0, base, hbase, seed, i, o, n, hi => by
      simpa using
        (superIterate_step_lt schedule 0 initial hinitial
          base hbase seed i o n hi)
  | k + 1, base, hbase, seed, i, o, n, hi => by
      have hfirst :
          initial base seed i n <
            superIterate schedule (k + 1) initial base seed i n :=
        lift_lt_superIterate_succ schedule initial hinitial
          k base hbase seed i i n hi
      have hsecond :
          superIterate schedule (k + 1) initial base seed i n <
            superIterate schedule ((k + 1) + 1) initial base seed o n :=
        superIterate_step_lt schedule (k + 1) initial hinitial
          base hbase seed i o n hi
      exact Nat.lt_trans hfirst hsecond

end BusyLean
