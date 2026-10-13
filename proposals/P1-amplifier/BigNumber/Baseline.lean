import BigNumber.BaselineDefs

namespace BigNumber.Baseline

/- The corresponding standard-library lemmas use `propext` internally.
These direct proofs keep the comparison theorem's axiom audit empty. -/
theorem max_eq_left_pure {a b : Nat} (h : b ≤ a) : max a b = a := by
  change (if a ≤ b then b else a) = a
  by_cases hab : a ≤ b
  · exact (if_pos hab).trans (Nat.le_antisymm h hab)
  · exact if_neg hab

theorem le_max_left_pure (a b : Nat) : a ≤ max a b := by
  cases Nat.le_total a b with
  | inl h => exact (Nat.max_eq_right h).symm ▸ h
  | inr h => exact (max_eq_left_pure h).symm ▸ Nat.le_refl a

theorem le_max_right_pure (a b : Nat) : b ≤ max a b := by
  cases Nat.le_total a b with
  | inl h => exact (Nat.max_eq_right h).symm ▸ Nat.le_refl b
  | inr h => exact (max_eq_left_pure h).symm ▸ h

theorem eval_maxBy {α : Type} (f : α → Nat) (xs : List α)
    (m : Nat) (best : α) (hbest : f best = m) :
    f (maxBy f m best xs) = xs.foldl (fun a x => max a (f x)) m := by
  induction xs generalizing m best with
  | nil => exact hbest
  | cons x xs ih =>
      change f (if m < f x then maxBy f (f x) x xs else maxBy f m best xs) =
        xs.foldl (fun a y => max a (f y)) (max m (f x))
      by_cases h : m < f x
      · rw [if_pos h, Nat.max_eq_right (Nat.le_of_lt h)]
        exact ih (f x) x rfl
      · rw [if_neg h, max_eq_left_pure (Nat.le_of_not_gt h)]
        exact ih m best hbest

theorem largest_eq_envelope (n : Nat) :
    largestSTLCNatRecNatOfDepth n = envelope n :=
  eval_maxBy eval (termsUpTo n) 0 .zero rfl

theorem contender_5_eq_envelope : contender_5 = envelope 42 :=
  largest_eq_envelope 42

theorem initial_le_foldMax {α : Type} (f : α → Nat) (xs : List α) (m : Nat) :
    m ≤ xs.foldl (fun a x => max a (f x)) m := by
  induction xs generalizing m with
  | nil => exact Nat.le_refl m
  | cons x xs ih =>
      exact Nat.le_trans (le_max_left_pure m (f x)) (ih (max m (f x)))

theorem member_le_foldMax {α : Type} (f : α → Nat) (xs : List α)
    (x : α) (hx : x ∈ xs) (m : Nat) :
    f x ≤ xs.foldl (fun a y => max a (f y)) m := by
  induction hx generalizing m with
  | head ys =>
      exact Nat.le_trans (le_max_right_pure m (f x))
        (initial_le_foldMax f ys (max m (f x)))
  | tail y _ ih => exact ih (max m (f y))

theorem envelope_bound {n : Nat} (t : Term) (h : t ∈ termsUpTo n) :
    eval t ≤ envelope n := member_le_foldMax eval (termsUpTo n) t h 0

/- These are small closed reduction tests, not evaluations of the contender. -/
example : lookup [10, 11, 12] 0 = some 12 := rfl
example : lookup [10, 11, 12] 1 = some 11 := rfl
example : lookup [10, 11, 12] 2 = some 10 := rfl
example : lookup [10, 11, 12] 3 = none := rfl
example : eval (.app .succ .zero) = 1 := rfl
example : eval (.app .zero .succ) = 0 := rfl
example : eval (.app (.lam .nat .nat (.var 0)) (.app .succ .zero)) = 1 := rfl
example : eval
    (.app
      (.app (.lam .nat (.arr .nat .nat) (.lam .nat .nat (.var 0)))
        (.app .succ .zero))
      (.app .succ (.app .succ .zero))) = 1 := rfl
example : eval
    (.app
      (.app (.lam .nat (.arr .nat .nat) (.lam .nat .nat (.var 1)))
        (.app .succ .zero))
      (.app .succ (.app .succ .zero))) = 2 := rfl
example : eval (.app (.lam .nat .nat .succ) .zero) = 0 := rfl
example : eval
    (.app
      (.app
        (.app (.natRec .nat) (.app .succ .zero))
        (.lam .nat (.arr .nat .nat)
          (.lam .nat .nat (.app .succ (.var 1)))))
      (.app .succ (.app .succ .zero))) = 3 := rfl
example : envelope 0 = 0 := rfl
example : envelope 1 = 0 := rfl
example : envelope 2 = 1 := rfl

end BigNumber.Baseline
