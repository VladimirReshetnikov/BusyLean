import BusyLean.SecondOrderReflection
import BusyLean.HyperReflectionFacts

/-!
# Growth facts for second-order diagonal hyperreflection

The proof discipline is the same as in `HyperReflectionFacts`: no monotonicity
in an oracle family is assumed. Reflection languages may inspect oracle values,
so such monotonicity is generally false. Every strict inequality follows an
explicit occurrence of a base lift or a selected child lift.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- A good transformer lift preserves progressive transformers and strictly
exceeds its input transformer at every visible coordinate. -/
def GoodLift (lift : TransformerLift) : Prop :=
  PreservesProgressive lift ∧ StrictlyInflationary lift

/-- A hyperlift preserves the class of good transformer lifts. -/
def PreservesGoodLifts (hyper : HyperLift) : Prop :=
  ∀ (lift : TransformerLift), GoodLift lift → GoodLift (hyper lift)

/-- A hyperlift strictly exceeds its input lift after both are applied to the
same progressive base transformer. -/
def StrictlyLiftInflationary (hyper : HyperLift) : Prop :=
  ∀ (lift : TransformerLift), GoodLift lift →
    ∀ (base : Transformer), Progressive base →
      ∀ (seed : Family) (i o n : Nat), i ≤ n →
        lift base seed i n < hyper lift base seed o n

/-- Pointwise splicing preserves the progressivity-preservation property. -/
theorem spliceLifts_preservesProgressive {ops : Nat → TransformerLift}
    (hops : ∀ i, PreservesProgressive (ops i)) :
    PreservesProgressive (spliceLifts ops) := by
  intro base hbase
  exact spliceTransformers_progressive (fun i => hops i base hbase)

/-- Pointwise splicing preserves strict inflationarity. -/
theorem spliceLifts_strictlyInflationary {ops : Nat → TransformerLift}
    (hops : ∀ i, StrictlyInflationary (ops i)) :
    StrictlyInflationary (spliceLifts ops) := by
  intro base hbase seed i o n hi
  change base seed i n < ops o base seed 0 n
  exact hops o base hbase seed i 0 n hi

/-- A splice of good lifts is good. -/
theorem spliceLifts_good {ops : Nat → TransformerLift}
    (hops : ∀ i, GoodLift (ops i)) :
    GoodLift (spliceLifts ops) :=
  ⟨spliceLifts_preservesProgressive (fun i => (hops i).1),
    spliceLifts_strictlyInflationary (fun i => (hops i).2)⟩

/-- The autonomous second-order lift preserves goodness. -/
theorem liftLift_preservesGoodLifts : PreservesGoodLifts liftLift := by
  intro lift hlift
  constructor
  · intro base hbase
    exact stageLift_progressive lift hlift.1 (lift base)
      (hlift.1 base hbase) index
  · intro base hbase seed i o n hi
    have hfirst : base seed i n < lift base seed i n :=
      hlift.2 base hbase seed i i n hi
    have hsecond :
        lift base seed i n < stageLift lift (lift base) index seed o n :=
      base_lt_stageLift lift hlift.1 hlift.2
        (lift base) (hlift.1 base hbase) index seed i o n hi
    exact Nat.lt_trans hfirst hsecond

/-- The autonomous second-order lift strictly exceeds its input lift. -/
theorem liftLift_strictlyLiftInflationary :
    StrictlyLiftInflationary liftLift := by
  intro lift hlift base hbase seed i o n hi
  exact base_lt_stageLift lift hlift.1 hlift.2
    (lift base) (hlift.1 base hbase) index seed i o n hi

/-- A hyperlift tree stage is good whenever its local hyperlift preserves good
lifts and its base lift is good. -/
theorem stageHyperLift_good (hyper : HyperLift)
    (hhyper : PreservesGoodLifts hyper)
    (base : TransformerLift) (hbase : GoodLift base) :
    (a : WTree Nat) → GoodLift (stageHyperLift hyper base a)
  | .leaf => hhyper base hbase
  | .node f => by
      apply hhyper
      exact spliceLifts_good
        (fun i => stageHyperLift_good hyper hhyper base hbase (f i))

/-- If a hyperlift is strict, then every tree stage strictly exceeds its base
lift. The node case follows child zero and then uses that child as coordinate
zero of the splice. -/
theorem base_lt_stageHyperLift (hyper : HyperLift)
    (hpres : PreservesGoodLifts hyper)
    (hstrict : StrictlyLiftInflationary hyper)
    (base : TransformerLift) (hbase : GoodLift base) :
    (a : WTree Nat) →
      ∀ (op : Transformer), Progressive op →
        ∀ (seed : Family) (i o n : Nat), i ≤ n →
          base op seed i n < stageHyperLift hyper base a op seed o n
  | .leaf, op, hop, seed, i, o, n, hi =>
      hstrict base hbase op hop seed i o n hi
  | .node f, op, hop, seed, i, o, n, hi => by
      have hchild :
          base op seed i n <
            stageHyperLift hyper base (f 0) op seed 0 n :=
        base_lt_stageHyperLift hyper hpres hstrict base hbase
          (f 0) op hop seed i 0 n hi
      have hsplice : GoodLift
          (spliceLifts (fun j => stageHyperLift hyper base (f j))) :=
        spliceLifts_good
          (fun j => stageHyperLift_good hyper hpres base hbase (f j))
      have hparent :
          stageHyperLift hyper base (f 0) op seed 0 n <
            stageHyperLift hyper base (.node f) op seed o n := by
        change
          spliceLifts (fun j => stageHyperLift hyper base (f j))
                op seed 0 n <
            hyper (spliceLifts (fun j => stageHyperLift hyper base (f j)))
                op seed o n
        exact hstrict
          (spliceLifts (fun j => stageHyperLift hyper base (f j)))
          hsplice op hop seed 0 o n (Nat.zero_le n)
      exact Nat.lt_trans hchild hparent

/-- Every second-order diagonal rank preserves goodness. -/
theorem diagonalHyperLift_preservesGoodLifts (schedule : WTree Nat) :
    ∀ k, PreservesGoodLifts (diagonalHyperLift schedule k)
  | 0 => liftLift_preservesGoodLifts
  | k + 1 => by
      intro base hbase
      exact stageHyperLift_good
        (diagonalHyperLift schedule k)
        (diagonalHyperLift_preservesGoodLifts schedule k)
        (diagonalHyperLift schedule k base)
        ((diagonalHyperLift_preservesGoodLifts schedule k) base hbase)
        schedule

/-- Every second-order diagonal rank strictly exceeds its original base lift. -/
theorem diagonalHyperLift_strictlyLiftInflationary
    (schedule : WTree Nat) :
    ∀ k, StrictlyLiftInflationary (diagonalHyperLift schedule k)
  | 0 => liftLift_strictlyLiftInflationary
  | k + 1 => by
      intro base hbase op hop seed i o n hi
      have hfirst :
          base op seed i n <
            diagonalHyperLift schedule k base op seed i n :=
        (diagonalHyperLift_strictlyLiftInflationary schedule k)
          base hbase op hop seed i i n hi
      have hbase' : GoodLift (diagonalHyperLift schedule k base) :=
        (diagonalHyperLift_preservesGoodLifts schedule k) base hbase
      have hsecond :
          diagonalHyperLift schedule k base op seed i n <
            stageHyperLift (diagonalHyperLift schedule k)
              (diagonalHyperLift schedule k base) schedule
              op seed o n :=
        base_lt_stageHyperLift
          (diagonalHyperLift schedule k)
          (diagonalHyperLift_preservesGoodLifts schedule k)
          (diagonalHyperLift_strictlyLiftInflationary schedule k)
          (diagonalHyperLift schedule k base) hbase'
          schedule op hop seed i o n hi
      exact Nat.lt_trans hfirst hsecond

/-- The second-order hierarchy is strictly increasing rank by rank. -/
theorem diagonalHyperLift_rank_lt_succ (schedule : WTree Nat) (k : Nat)
    (base : TransformerLift) (hbase : GoodLift base)
    (op : Transformer) (hop : Progressive op)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    diagonalHyperLift schedule k base op seed i n <
      diagonalHyperLift schedule (k + 1) base op seed o n := by
  have hbase' : GoodLift (diagonalHyperLift schedule k base) :=
    (diagonalHyperLift_preservesGoodLifts schedule k) base hbase
  exact base_lt_stageHyperLift
    (diagonalHyperLift schedule k)
    (diagonalHyperLift_preservesGoodLifts schedule k)
    (diagonalHyperLift_strictlyLiftInflationary schedule k)
    (diagonalHyperLift schedule k base) hbase'
    schedule op hop seed i o n hi

end BusyLean
