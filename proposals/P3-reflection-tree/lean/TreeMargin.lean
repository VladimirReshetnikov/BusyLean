import Hierarchy
import OracleFacts

/-!
# A fivefold exponential margin over the exact baseline

The proof uses a finite certificate that counts successor nodes along
zeroth branches. It never evaluates a contender or an ordinal-shaped tree.
-/

namespace Biggest

def marginStep (n x : Nat) : Nat := 2 ^ (x + (n + 2))

def marginTower (n k x : Nat) : Nat := treeIter (marginStep n) k x

theorem margin_step_mono (n : Nat) {x y : Nat} (h : x ≤ y) :
    marginStep n x ≤ marginStep n y :=
  Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (Nat.add_le_add_right h (n + 2))

theorem margin_zero_mem (n : Nat) : 0 ∈ natsUpTo (n + 1) := by
  induction n with
  | zero => exact List.Mem.head []
  | succ n ih => exact List.Mem.tail _ ih

theorem margin_limit0_le (s : Nat → Stage) (n : Nat) :
    hierarchy (s 0) n ≤ hierarchy (.lim s) n :=
  Nat.le_trans
    (le_maximum_of_mem (fun k => hierarchy (s k) n) 0
      (natsUpTo (n + 1)) (margin_zero_mem n))
    (Nat.le_succ _)

theorem margin_successor_step (a : Stage) (n : Nat) :
    marginStep n (hierarchy a (n + 1)) ≤ hierarchy (.succ a) (n + 1) :=
  oracle_power_le_reflect (hierarchy a) (n + 1)

/-- A finite path using only successor edges and zeroth limit branches. -/
inductive MarginPath : Nat → Stage → Prop where
  | base (a : Stage) : MarginPath 0 a
  | next {k : Nat} {a : Stage} : MarginPath k a → MarginPath (k + 1) (.succ a)
  | limit0 {k : Nat} {s : Nat → Stage} : MarginPath k (s 0) → MarginPath k (.lim s)

theorem margin_path_bound (n : Nat) {k : Nat} {a : Stage} (h : MarginPath k a) :
    k ≠ 0 → marginTower n k (baseline n) ≤ hierarchy a (n + 1) := by
  induction h with
  | base a =>
    intro impossible
    exact False.elim (impossible rfl)
  | @next k a path ih =>
    intro _
    cases k with
    | zero => exact baseline_power_le_reflect (hierarchy a) n
    | succ k =>
      exact Nat.le_trans (margin_step_mono n (ih (Nat.noConfusion)))
        (margin_successor_step a n)
  | @limit0 k s path ih =>
    intro positive
    exact Nat.le_trans (ih positive) (margin_limit0_le s (n + 1))

theorem finalStage_five_successors : MarginPath 5 finalStage := by
  apply MarginPath.next
  apply MarginPath.next
  apply MarginPath.limit0
  apply MarginPath.next
  apply MarginPath.next
  apply MarginPath.limit0
  apply MarginPath.next
  exact MarginPath.base _

/-- Five iterations of x ↦ 2^(x+44), beginning at the exact Contender 5. -/
theorem contender_6_fivefold_margin :
    marginTower 42 5 (baseline 42) ≤ contender_6 :=
  margin_path_bound 42 finalStage_five_successors (Nat.noConfusion)

end Biggest
