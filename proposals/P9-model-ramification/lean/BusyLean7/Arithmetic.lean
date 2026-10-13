import BusyLean7.Definitions
import Lean

/-! Arithmetic lemmas. Source is supplied for checking, not reported as checked. -/
namespace BusyLean7

/-- Elementary monotonicity from adjacent inequalities. -/
theorem monotone_of_step (f : Nat → Nat) (hf : ∀ k, f k ≤ f (k + 1))
    {m n : Nat} (h : m ≤ n) : f m ≤ f n := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact Nat.le_refl _
  | succ n ih =>
      by_cases hmn : m ≤ n
      · exact Nat.le_trans (ih hmn) (hf n)
      · have hm : m = n + 1 := by omega
        subst m
        exact Nat.le_refl _

theorem self_lt_pow2 (n : Nat) : n < BigNumber.pow2 n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [BigNumber.pow2]
      omega

theorem pow2_mono {m n : Nat} (h : m ≤ n) :
    BigNumber.pow2 m ≤ BigNumber.pow2 n := by
  apply monotone_of_step BigNumber.pow2 _ h
  intro k
  simp only [BigNumber.pow2]
  omega

theorem le_iter (f : Nat → Nat) (hf : ∀ x, x ≤ f x) (k x : Nat) :
    x ≤ iter f k x := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact Nat.le_trans ih (hf _)

theorem iter_mono_input (f : Nat → Nat)
    (hf : ∀ {a b}, a ≤ b → f a ≤ f b) (k : Nat)
    {x y : Nat} (h : x ≤ y) : iter f k x ≤ iter f k y := by
  induction k with
  | zero => exact h
  | succ k ih => exact hf ih

theorem iter_mono_count (f : Nat → Nat) (hf : ∀ x, x ≤ f x)
    {k l : Nat} (h : k ≤ l) (x : Nat) : iter f k x ≤ iter f l x :=
  monotone_of_step (fun j => iter f j x) (fun _ => hf _) h

theorem self_lt_theta (x : Nat) : x < theta x := by
  have h := le_iter BigNumber.pow2 (fun y => Nat.le_of_lt (self_lt_pow2 y))
    (x + 1) (x + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self x) h

theorem theta_mono {x y : Nat} (h : x ≤ y) : theta x ≤ theta y := by
  have hs : x + 1 ≤ y + 1 := Nat.succ_le_succ h
  exact Nat.le_trans
    (iter_mono_input BigNumber.pow2 (fun h => pow2_mono h) (x + 1) hs)
    (iter_mono_count BigNumber.pow2 (fun z => Nat.le_of_lt (self_lt_pow2 z)) hs _)

theorem theta_iter_mono {x y : Nat} (h : x ≤ y) (k : Nat) :
    iter theta k x ≤ iter theta k y :=
  iter_mono_input theta (fun h => theta_mono h) k h

/-- An iteration identity used to expose a lower bound without evaluation. -/
theorem iter_succ_input (f : Nat → Nat) (k x : Nat) :
    iter f k (f x) = iter f (k + 1) x := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg f ih

end BusyLean7
