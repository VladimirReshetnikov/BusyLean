import BusyLean7.Semantics

/-! Finite-maximum reflection, lifting uniform witnesses, and diagonal escape. -/
namespace BusyLean7
open BigNumber (Term)

theorem le_max_left : ∀ a b : Nat, a ≤ BigNumber.maxN a b
  | 0, b => Nat.zero_le b
  | a + 1, 0 => Nat.le_refl _
  | a + 1, b + 1 => Nat.succ_le_succ (le_max_left a b)

theorem le_max_right : ∀ a b : Nat, b ≤ BigNumber.maxN a b
  | 0, b => Nat.le_refl b
  | a + 1, 0 => Nat.zero_le _
  | a + 1, b + 1 => Nat.succ_le_succ (le_max_right a b)

theorem le_list_max {A : Type} (f : A → Nat) {x : A} :
    ∀ {xs : List A}, x ∈ xs → f x ≤ BigNumber.maximum f xs
  | _ :: _, .head _ => le_max_left _ _
  | y :: _, .tail _ h => Nat.le_trans (le_list_max f h) (le_max_right (f y) _)

theorem le_prefix (f : Nat → Nat) : ∀ {i n : Nat}, i ≤ n →
    f i ≤ BusyLean.W.prefixMax f n
  | _, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | i, n + 1, h => by
      cases Nat.lt_or_eq_of_le h with
      | inl hlt => exact Nat.le_trans (le_prefix f (Nat.le_of_lt_succ hlt))
          (le_max_left _ _)
      | inr heq => rw [heq]; exact le_max_right _ _

theorem bound_lt_reflect (M : Model) (fs : Family) (n m : Nat)
    (h : m ≤ BigNumber.maxN (BusyLean.W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (eval M fs n) (BigNumber.allTerms n))) :
    m < reflect M fs n := by
  unfold reflect
  omega

theorem eval_lt_reflect (M : Model) (fs : Family) {n : Nat} {t : Term}
    (ht : t ∈ BigNumber.allTerms n) : eval M fs n t < reflect M fs n :=
  bound_lt_reflect M fs n _
    (Nat.le_trans (le_list_max (eval M fs n) ht) (le_max_right _ _))

theorem oracle_lt_reflect (M : Model) (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflect M fs n :=
  bound_lt_reflect M fs n _
    (Nat.le_trans (le_prefix (fun j => fs j n) hi) (le_max_left _ _))

theorem input_lt_reflect (M : Model) (fs : Family) (n : Nat) :
    n < reflect M fs n := by
  unfold reflect
  omega

theorem child_lt_stage (M : Model) (seed : Family) (f : Nat → Tree)
    {i n : Nat} (hi : i ≤ n) :
    stage M seed (f i) n < stage M seed (.node f) n :=
  oracle_lt_reflect M (fun j => stage M seed (f j)) hi

/-- A single oracle-INDEPENDENT certificate works at every forest node. -/
theorem uniform_lt_stage (M : Model) (seed : Family) (a : Tree)
    {n m : Nat} {t : Term} (ht : t ∈ BigNumber.allTerms n)
    (hm : ∀ fs, eval M fs n t = m) : m < stage M seed a n := by
  cases a with
  | leaf =>
      change m < reflect M seed n
      rw [← hm seed]
      exact eval_lt_reflect M seed ht
  | node f =>
      let fs : Family := fun i => stage M seed (f i)
      change m < reflect M fs n
      rw [← hm fs]
      exact eval_lt_reflect M fs ht

theorem amplified_zero_lt_value (M : Model) {n : Nat} (hn : 11 ≤ n) :
    theta (M.lowerStage 0 BusyLean.p5Family (M.lowerTree 0) n) < value M n :=
  uniform_lt_stage M BusyLean.p5Family (modelIndex M)
    (zero_certificate_mem hn) (fun fs => eval_amplified_zero M fs n)

theorem amplified_input_lt_value (M : Model) {n : Nat} (hn : 11 ≤ n) :
    theta (M.lowerStage n BusyLean.p5Family (M.lowerTree n) n) < value M n :=
  uniform_lt_stage M BusyLean.p5Family (modelIndex M)
    (input_certificate_mem hn) (fun fs => eval_amplified_input M fs n)

/-- No fixed program of this object language eventually majorizes its own
reflection, even when the common oracle family is allowed to vary with n. -/
theorem no_eventual_self_majorant (M : Model) (oracles : Nat → Family) (t : Term) :
    ¬ ∃ N, ∀ n, N ≤ n → reflect M (oracles n) n ≤ eval M (oracles n) n t := by
  intro h
  obtain ⟨N, hN⟩ := h
  let n := Nat.max N (termRank t)
  have h0 : N ≤ n := Nat.le_max_left _ _
  have h1 : termRank t ≤ n := Nat.le_max_right _ _
  have hlt := eval_lt_reflect M (oracles n) (term_mem t n h1)
  exact Nat.not_lt_of_ge (hN n h0) hlt

end BusyLean7
