import Oracle

namespace Biggest

theorem eval_quote (f : Nat → Nat) (n : Nat) (t : Term) :
    evalExpr f n (.quote t) = eval t := rfl

theorem quote_mem (n : Nat) (t : Term) (ht : t ∈ termsUpTo n) :
    Expr.quote t ∈ exprsUpTo (n + 1) := by
  change Expr.quote t ∈ (termsUpTo n).map Expr.quote ++ _
  exact memAppendLeft _ (memMap Expr.quote ht)

theorem exponent_margin (m n : Nat) : m < 2 ^ (m + n + 1) :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.le_add_right m n) (Nat.le_succ (m + n)))
    Nat.lt_two_pow_self

theorem reflect_gt_max (f : Nat → Nat) (n : Nat) :
    max (f n) (maximum (evalExpr f n) (exprsUpTo n)) < reflect f n :=
  exponent_margin _ n

theorem reflect_gt_oracle (f : Nat → Nat) (n : Nat) : f n < reflect f n :=
  Nat.lt_of_le_of_lt (leMaxLeft _ _) (reflect_gt_max f n)

theorem reflect_gt_member (f : Nat → Nat) (n : Nat) (e : Expr)
    (he : e ∈ exprsUpTo n) : evalExpr f n e < reflect f n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (le_maximum_of_mem _ e _ he) (leMaxRight _ _))
    (reflect_gt_max f n)

theorem baseline_le_oracle_max (f : Nat → Nat) (n : Nat) :
    baseline n ≤ maximum (evalExpr f (n + 1)) (exprsUpTo (n + 1)) := by
  rw [baseline_eq_maximum]
  apply maximum_le
  intro t ht
  exact le_maximum_of_mem (evalExpr f (n + 1)) (Expr.quote t) _ (quote_mem n t ht)

theorem baseline_lt_reflect (f : Nat → Nat) (n : Nat) :
    baseline n < reflect f (n + 1) :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (baseline_le_oracle_max f n) (leMaxRight _ _))
    (reflect_gt_max f (n + 1))

theorem baseline_power_le_reflect (f : Nat → Nat) (n : Nat) :
    2 ^ (baseline n + (n + 2)) ≤ reflect f (n + 1) :=
  Nat.pow_le_pow_right (Nat.zero_lt_succ 1)
    (Nat.add_le_add_right
      (Nat.le_trans (baseline_le_oracle_max f n) (leMaxRight _ _))
      (n + 2))

theorem oracle_power_le_reflect (f : Nat → Nat) (n : Nat) :
    2 ^ (f n + n + 1) ≤ reflect f n :=
  Nat.pow_le_pow_right (Nat.zero_lt_succ 1)
    (Nat.add_le_add_right (Nat.add_le_add_right (leMaxLeft _ _) n) 1)

theorem lower_bound_power_le_reflect (f : Nat → Nat) (n b : Nat)
    (h : b ≤ max (f n) (maximum (evalExpr f n) (exprsUpTo n))) :
    2 ^ (b + (n + 1)) ≤ reflect f n :=
  Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (Nat.add_le_add_right h (n + 1))

end Biggest
