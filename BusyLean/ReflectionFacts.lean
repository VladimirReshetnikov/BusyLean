import BusyLean.Reflection
import BigNumber.Proofs

/-! # Inequalities for reflection and forest reflection

All results are direct inequalities. Monotonicity of reflection in its oracle
is never assumed (it fails in general: a program may test oracle values).
-/

namespace BusyLean.W

open BigNumber (Term WTree)

/-! ## Basic inequalities -/

theorem le_prefixMax (g : Nat → Nat) : ∀ {i k : Nat}, i ≤ k → g i ≤ prefixMax g k
  | _, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | i, k + 1, h => by
      cases Nat.lt_or_eq_of_le h with
      | inl hlt =>
          exact Nat.le_trans (le_prefixMax g (Nat.le_of_lt_succ hlt))
            (BigNumber.le_maxN_left _ _)
      | inr heq => rw [heq]; exact BigNumber.le_maxN_right _ _

theorem le_maximum {α : Type} (f : α → Nat) {x : α} :
    ∀ {l : List α}, x ∈ l → f x ≤ BigNumber.maximum f l
  | _ :: _, .head _ => BigNumber.le_maxN_left _ _
  | y :: _, .tail _ h => Nat.le_trans (le_maximum f h) (BigNumber.le_maxN_right (f y) _)

/-- The core of reflection: a bound `m` on the reflected maximum is exceeded. -/
theorem lt_reflect {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (evalWith fs) (BigNumber.allTerms n))) :
    m < reflect fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible oracle value is exceeded. -/
theorem oracle_lt_reflect (fs : Family) {i n : Nat} (hi : i ≤ n) : fs i n < reflect fs n :=
  lt_reflect (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

/-- Every program of depth `≤ n`, run with the oracle, is exceeded. -/
theorem evalWith_lt_reflect (fs : Family) {n : Nat} {t : Term}
    (ht : t ∈ BigNumber.allTerms n) : evalWith fs t < reflect fs n :=
  lt_reflect (Nat.le_trans (le_maximum (evalWith fs) ht) (BigNumber.le_maxN_right _ _))

/-- The input itself is exceeded. -/
theorem input_lt_reflect (fs : Family) (n : Nat) : n < reflect fs n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

/-- Each visible child stage is strictly exceeded by its parent. -/
theorem stage_child_lt (seed : Family) (f : Nat → WTree Nat) {i n : Nat} (hi : i ≤ n) :
    stage seed (f i) n < stage seed (.node f) n :=
  oracle_lt_reflect (fun j => stage seed (f j)) hi

/-- Every visible seed value is strictly exceeded at a leaf. -/
theorem seed_lt_stage_leaf (seed : Family) {i n : Nat} (hi : i ≤ n) :
    seed i n < stage seed .leaf n :=
  oracle_lt_reflect seed hi

end BusyLean.W
