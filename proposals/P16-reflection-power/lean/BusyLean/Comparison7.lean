import BusyLean.Contender7
import BusyLean.Comparison

/-!
# Contender 7: comparison theorems

The central invariant says that a scheduler, when run through the universal
`index`, exceeds every visible entry of its seed family.  The existing `stage`
satisfies the invariant.  One reflection-order lift preserves it and is
strictly larger at `index`; induction therefore gives a strict hierarchy.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- `S` exceeds every visible seed entry when scheduled through `index`. -/
def IndexDominates (S : StageOperator) : Prop :=
  ∀ (seed : Family) {i n : Nat}, i ≤ n → seed i n < S seed index n

/-- The existing forest scheduler dominates its seed at the universal index. -/
theorem seed_lt_stage_index (seed : Family) {i n : Nat} (hi : i ≤ n) :
    seed i n < stage seed index n := by
  have h1 : seed i n < stage seed .leaf n :=
    seed_lt_stage_leaf seed hi
  have h2 :
      stage seed (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
        stage seed (treesOfDepth 0) n :=
    stage_child_lt seed _ (Nat.zero_le n)
  have h3 : stage seed (treesOfDepth 0) n < stage seed index n :=
    stage_child_lt seed treesOfDepth (Nat.zero_le n)
  rw [first_tree_leaf] at h2
  exact Nat.lt_trans h1 (Nat.lt_trans h2 h3)

/-- The base scheduler has the domination invariant. -/
theorem stage_indexDominates : IndexDominates stage := by
  intro seed i n hi
  exact seed_lt_stage_index seed hi

/-- A promoted child is visible to, and strictly below, its promoted parent. -/
theorem liftStage_child_lt {S : StageOperator} (hS : IndexDominates S)
    (seed : Family) (f : Nat → WTree Nat) {i n : Nat} (hi : i ≤ n) :
    liftStage S seed (f i) n < liftStage S seed (.node f) n := by
  change liftStage S seed (f i) n <
    S (fun j => liftStage S seed (f j)) index n
  exact hS (fun j => liftStage S seed (f j)) hi

/-- For every invariant-preserving scheduler, its leaf lift is strictly below
its lift through the universal index. -/
theorem liftStage_leaf_lt_index {S : StageOperator} (hS : IndexDominates S)
    (seed : Family) (n : Nat) :
    liftStage S seed .leaf n < liftStage S seed index n := by
  have h1 :
      liftStage S seed (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
        liftStage S seed (treesOfDepth 0) n :=
    liftStage_child_lt hS seed _ (Nat.zero_le n)
  have h2 :
      liftStage S seed (treesOfDepth 0) n < liftStage S seed index n :=
    liftStage_child_lt hS seed treesOfDepth (Nat.zero_le n)
  rw [first_tree_leaf] at h1
  exact Nat.lt_trans h1 h2

/-- One order lift preserves the domination invariant. -/
theorem liftStage_indexDominates {S : StageOperator} (hS : IndexDominates S) :
    IndexDominates (liftStage S) := by
  intro seed i n hi
  have h0 : seed i n < S seed index n := hS seed hi
  have h0' : seed i n < liftStage S seed .leaf n := by
    change seed i n < S seed index n
    exact h0
  exact Nat.lt_trans h0' (liftStage_leaf_lt_index hS seed n)

/-- Every finite scheduler order retains the domination invariant. -/
theorem stageOrder_indexDominates : ∀ k, IndexDominates (stageOrder k)
  | 0 => stage_indexDominates
  | k + 1 => liftStage_indexDominates (stageOrder_indexDominates k)

/-- Every successor scheduler order is strictly larger at the universal index. -/
theorem stageOrder_step (seed : Family) (k n : Nat) :
    stageOrder k seed index n < stageOrder (k + 1) seed index n := by
  change liftStage (stageOrder k) seed .leaf n <
    liftStage (stageOrder k) seed index n
  exact liftStage_leaf_lt_index (stageOrder_indexDominates k) seed n

/-- Order zero is strictly below every positive order. -/
theorem stageOrder_zero_lt_succ (seed : Family) (n : Nat) :
    ∀ k, stageOrder 0 seed index n < stageOrder (Nat.succ k) seed index n
  | 0 => by
      simpa using stageOrder_step seed 0 n
  | k + 1 => by
      exact Nat.lt_trans (stageOrder_zero_lt_succ seed n k)
        (by simpa using stageOrder_step seed (k + 1) n)

/-- **Required comparison:** the current repository contender is strictly below
Contender 7.  The proof unfolds only the successor guard, not the huge P5
height. -/
theorem contender_6_lt_contender_7 : contender_6 < contender_7 := by
  change stageOrder 0 p5Family index 42 <
    stageOrder (Nat.succ (42 + p5Family 0 42)) p5Family index 42
  exact stageOrder_zero_lt_succ p5Family 42 (42 + p5Family 0 42)

/-- The exact Contender 5 port is also strictly below Contender 7. -/
theorem contender_5_lt_contender_7 : contender_5 < contender_7 :=
  Nat.lt_trans contender_5_lt_contender_6 contender_6_lt_contender_7

/-- Proposal P5's number is strictly below Contender 7. -/
theorem p5_lt_contender_7 : BigNumber.contender_6 < contender_7 :=
  Nat.lt_trans p5_lt_contender_6 contender_6_lt_contender_7

end BusyLean
