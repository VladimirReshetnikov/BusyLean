import BusyLean.HyperReflection
import BusyLean.MetaReflectionFacts

/-!
# Strict growth of diagonal hyperreflection

The proofs never assume monotonicity in an oracle; that property is false for
reflection because programs can branch on oracle values.  Every inequality is
instead witnessed by an explicit occurrence of a seed transformer or a child
transformer.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- A transformer lift preserves progressivity. -/
def PreservesProgressive (lift : TransformerLift) : Prop :=
  ∀ (op : Transformer), Progressive op → Progressive (lift op)

/-- A transformer lift strictly exceeds its input transformer at every visible
coordinate and the same numerical input. -/
def StrictlyInflationary (lift : TransformerLift) : Prop :=
  ∀ (op : Transformer), Progressive op →
    ∀ (seed : Family) (i o n : Nat), i ≤ n →
      op seed i n < lift op seed o n

/-- Ordinary autonomous lifting preserves progressivity. -/
theorem liftTransformer_preservesProgressive :
    PreservesProgressive liftTransformer := by
  intro op hop
  exact liftTransformer_progressive hop

/-- Ordinary autonomous lifting strictly exceeds its input transformer. -/
theorem liftTransformer_strictlyInflationary :
    StrictlyInflationary liftTransformer := by
  intro op hop seed i o n hi
  exact transformer_lt_lift_at hop seed hi

/-- A tree stage preserves progressivity whenever its local lift does. -/
theorem stageLift_progressive (lift : TransformerLift)
    (hlift : PreservesProgressive lift) (base : Transformer)
    (hbase : Progressive base) :
    (a : WTree Nat) → Progressive (stageLift lift base a)
  | .leaf => hlift base hbase
  | .node f =>
      hlift
        (spliceTransformers (fun i => stageLift lift base (f i)))
        (spliceTransformers_progressive
          (fun i => stageLift_progressive lift hlift base hbase (f i)))

/-- If the local lift is strict, then every tree stage strictly exceeds its
base transformer.  The node case follows child zero explicitly and then uses
that child as coordinate zero of the splice. -/
theorem base_lt_stageLift (lift : TransformerLift)
    (hpres : PreservesProgressive lift)
    (hstrict : StrictlyInflationary lift)
    (base : Transformer) (hbase : Progressive base) :
    (a : WTree Nat) → ∀ (seed : Family) (i o n : Nat), i ≤ n →
      base seed i n < stageLift lift base a seed o n
  | .leaf, seed, i, o, n, hi =>
      hstrict base hbase seed i o n hi
  | .node f, seed, i, o, n, hi => by
      have hchild :
          base seed i n < stageLift lift base (f 0) seed 0 n :=
        base_lt_stageLift lift hpres hstrict base hbase
          (f 0) seed i 0 n hi
      have hsplice : Progressive
          (spliceTransformers (fun j => stageLift lift base (f j))) :=
        spliceTransformers_progressive
          (fun j => stageLift_progressive lift hpres base hbase (f j))
      have hparent := hstrict
        (spliceTransformers (fun j => stageLift lift base (f j)))
        hsplice seed 0 o n (Nat.zero_le n)
      exact Nat.lt_trans hchild hparent

/-- Every diagonal rank preserves progressivity. -/
theorem diagonalLift_preservesProgressive (schedule : WTree Nat) :
    ∀ k, PreservesProgressive (diagonalLift schedule k)
  | 0 => liftTransformer_preservesProgressive
  | k + 1 => by
      intro base hbase
      exact stageLift_progressive
        (diagonalLift schedule k)
        (diagonalLift_preservesProgressive schedule k)
        (diagonalLift schedule k base)
        ((diagonalLift_preservesProgressive schedule k) base hbase)
        schedule

/-- Every diagonal rank strictly exceeds its original base transformer. -/
theorem diagonalLift_strictlyInflationary (schedule : WTree Nat) :
    ∀ k, StrictlyInflationary (diagonalLift schedule k)
  | 0 => liftTransformer_strictlyInflationary
  | k + 1 => by
      intro base hbase seed i o n hi
      have hfirst :
          base seed i n < diagonalLift schedule k base seed i n :=
        (diagonalLift_strictlyInflationary schedule k)
          base hbase seed i i n hi
      have hbase' : Progressive (diagonalLift schedule k base) :=
        (diagonalLift_preservesProgressive schedule k) base hbase
      have hsecond :
          diagonalLift schedule k base seed i n <
            stageLift (diagonalLift schedule k)
              (diagonalLift schedule k base) schedule seed o n :=
        base_lt_stageLift
          (diagonalLift schedule k)
          (diagonalLift_preservesProgressive schedule k)
          (diagonalLift_strictlyInflationary schedule k)
          (diagonalLift schedule k base) hbase'
          schedule seed i o n hi
      exact Nat.lt_trans hfirst hsecond

/-- The hierarchy is strictly increasing rank by rank. -/
theorem diagonalLift_rank_lt_succ (schedule : WTree Nat) (k : Nat)
    (base : Transformer) (hbase : Progressive base)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    diagonalLift schedule k base seed i n <
      diagonalLift schedule (k + 1) base seed o n := by
  have hbase' : Progressive (diagonalLift schedule k base) :=
    (diagonalLift_preservesProgressive schedule k) base hbase
  exact base_lt_stageLift
    (diagonalLift schedule k)
    (diagonalLift_preservesProgressive schedule k)
    (diagonalLift_strictlyInflationary schedule k)
    (diagonalLift schedule k base) hbase'
    schedule seed i o n hi

end BusyLean
