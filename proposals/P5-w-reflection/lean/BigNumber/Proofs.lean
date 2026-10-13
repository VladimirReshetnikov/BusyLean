import BigNumber.Definitions

/-! Explicit proof terms. No simp, omega, native_decide, or extensionality. -/
namespace BigNumber

theorem le_maxN_left : ∀ a b : Nat, a ≤ maxN a b
  | 0, b => Nat.zero_le b
  | a+1, 0 => Nat.le_refl (a+1)
  | a+1, b+1 => Nat.succ_le_succ (le_maxN_left a b)

theorem le_maxN_right : ∀ a b : Nat, b ≤ maxN a b
  | 0, b => Nat.le_refl b
  | a+1, 0 => Nat.zero_le (a+1)
  | a+1, b+1 => Nat.succ_le_succ (le_maxN_right a b)

theorem le_add (a : Nat) : ∀ b : Nat, a ≤ a+b
  | 0 => Nat.le_refl a
  | b+1 => Nat.le.step (le_add a b)

theorem old_lt_seed (n : Nat) : oldMaximum n < seed n :=
  Nat.lt_succ_of_le
    (Nat.le_trans (le_maxN_left (oldMaximum n) (wMaximum n))
      (Nat.le_trans (le_maxN_left (envelope n) (pow2 (n+1)))
        (le_maxN_right n (maxN (envelope n) (pow2 (n+1))))))

theorem self_lt_seed (n : Nat) : n < seed n :=
  Nat.lt_succ_of_le (le_maxN_left n (maxN (envelope n) (pow2 (n+1))))

theorem pow2_lt_seed (n : Nat) : pow2 (n+1) < seed n :=
  Nat.lt_succ_of_le
    (Nat.le_trans (le_maxN_right (envelope n) (pow2 (n+1)))
      (le_maxN_right n (maxN (envelope n) (pow2 (n+1)))))

theorem row_le_next (f : Nat → Nat) (k n : Nat) :
    rows f k n ≤ rows f (k+1) n :=
  Nat.le_trans
    (le_add (rows f k n) (iterate (rows f k) (n+1) (n+1)))
    (le_add (rows f k n + iterate (rows f k) (n+1) (n+1)) 1)

theorem base_le_rows (f : Nat → Nat) : ∀ k n, f n ≤ rows f k n
  | 0, n => Nat.le_refl (f n)
  | k+1, n => Nat.le_trans (base_le_rows f k n) (row_le_next f k n)

theorem base_le_jump (f : Nat → Nat) (n : Nat) : f n ≤ jump f n :=
  base_le_rows f n n

theorem seed_le_ranks : ∀ k n, seed n ≤ ranks k n
  | 0, n => Nat.le_refl (seed n)
  | k+1, n => Nat.le_trans (seed_le_ranks k n) (base_le_jump (ranks k) n)

theorem seed_le_diagonal (n : Nat) : seed n ≤ diagonal n :=
  seed_le_ranks n n

theorem self_lt_diagonal (n : Nat) : n < diagonal n :=
  Nat.lt_of_lt_of_le (self_lt_seed n) (seed_le_diagonal n)

theorem self_le_diagonal (n : Nat) : n ≤ diagonal n :=
  Nat.le_of_lt (self_lt_diagonal n)

theorem le_iterate (f : Nat → Nat) (hf : ∀ x, x ≤ f x) :
    ∀ k x, x ≤ iterate f k x
  | 0, x => Nat.le_refl x
  | k+1, x => Nat.le_trans (hf x) (le_iterate f hf k (f x))

/-- Exact strict comparison with the numerical port of the old selector. -/
def contender_5 : Nat := oldMaximum 42

theorem contender_5_lt_contender_6 : contender_5 < contender_6 :=
  Nat.lt_of_lt_of_le
    (Nat.lt_of_lt_of_le (old_lt_seed 42) (seed_le_diagonal 42))
    (le_iterate diagonal self_le_diagonal 41 (diagonal 42))

end BigNumber
