import Trees

/-!
# Structural growth lemmas

These lemmas apply to any numerical interpretation that strictly increases
at successor nodes and above the zeroth child of every limit node.
No monotonicity assumption about the oracle, or about ordinal values of
trees, occurs in any statement.
-/

namespace Biggest

variable (value : Stage → Nat)
variable (succ_increases : ∀ a, value a < value (.succ a))
variable (limit_increases : ∀ s : Nat → Stage, value (s 0) < value (.lim s))

include succ_increases limit_increases in
theorem higherTower_increases (f : Stage → Stage) (a : Stage) :
    value a < value (higherTower f a) := by
  apply Nat.lt_trans ?_ (succ_increases _)
  apply Nat.lt_trans ?_ (limit_increases _)
  change value a < value (.succ (.lim (fun k => treeIter f k a)))
  apply Nat.lt_trans ?_ (succ_increases _)
  exact limit_increases (fun k => treeIter f k a)

include limit_increases in
theorem stageIter_extensive (f : Stage → Stage)
    (f_extensive : ∀ a, value a ≤ value (f a)) (t a : Stage) :
    value a ≤ value (stageIter f t a) := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih => exact Nat.le_trans ih (f_extensive _)
  | lim s ih =>
    exact Nat.le_trans (ih 0)
      (Nat.le_of_lt (limit_increases (fun k => stageIter f (s k) a)))

include succ_increases limit_increases in
theorem promoteTreeFunction_increases (f : Stage → Stage) (a : Stage) :
    value a < value (promoteTreeFunction f a) := by
  apply Nat.lt_of_le_of_lt ?_ (succ_increases _)
  apply stageIter_extensive value limit_increases
  intro x
  exact Nat.le_of_lt (higherTower_increases value succ_increases limit_increases f x)

include succ_increases limit_increases in
theorem promotedTreeFunction_increases (a : Stage) :
    value a < value (promotedTreeFunction a) := by
  apply Nat.lt_trans ?_ (succ_increases _)
  apply Nat.lt_trans ?_ (limit_increases _)
  exact promoteTreeFunction_increases value succ_increases limit_increases
    startingTreeFunction a

include succ_increases limit_increases in
theorem finalStage_exceeds_gammaTree : value gammaTree < value finalStage := by
  have hseed : value gammaTree < value (promotedTreeFunction gammaTree) :=
    promotedTreeFunction_increases value succ_increases limit_increases gammaTree
  have hext : ∀ a, value a ≤ value (promotedTreeFunction a) := by
    intro a
    exact Nat.le_of_lt
      (promotedTreeFunction_increases value succ_increases limit_increases a)
  have hiter := stageIter_extensive value limit_increases
    promotedTreeFunction hext (promotedTreeFunction gammaTree)
    (promotedTreeFunction gammaTree)
  exact Nat.lt_trans (Nat.lt_of_lt_of_le hseed hiter) (succ_increases _)

end Biggest
