import BigNumber.AmplifierDefs

namespace BigNumber.Amplifier

theorem iterate_congr {α : Type u} {f g : α → α}
    (h : ∀ x, f x = g x) (k : Nat) (x : α) :
    iterate f k x = iterate g k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      exact (ih (f x)).trans (congrArg (iterate g k) (h x))

theorem iterate_ge {f : Nat → Nat} (h : ∀ x, x ≤ f x)
    (k x : Nat) : x ≤ iterate f k x := by
  induction k generalizing x with
  | zero => exact Nat.le_refl x
  | succ k ih => exact Nat.le_trans (h x) (ih (f x))

theorem iterate_add_le {f : Nat → Nat} (h : ∀ x, x + 1 ≤ f x)
    (k x : Nat) : x + k ≤ iterate f k x := by
  induction k generalizing x with
  | zero => exact Nat.le_refl x
  | succ k ih =>
      calc
        x + (k + 1) = (x + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        _ ≤ f x + k := Nat.add_le_add_right (h x) k
        _ ≤ iterate f k (f x) := ih (f x)

/-- No monotonicity assumption on the base is needed. -/
theorem base_le_fast (b : Nat → Nat) (hb : ∀ n, n ≤ b n)
    (a : Tree) (n : Nat) : b n ≤ fast b a n := by
  induction a generalizing n with
  | zero => exact Nat.le_refl (b n)
  | succ a ih =>
      exact Nat.le_trans (ih n)
        (iterate_ge (fun m => Nat.le_trans (hb m) (ih m)) n (fast b a n))
  | limit f ih => exact ih n n

theorem fast_inflationary (b : Nat → Nat) (hb : ∀ n, n ≤ b n)
    (a : Tree) (n : Nat) : n ≤ fast b a n :=
  Nat.le_trans (hb n) (base_le_fast b hb a n)

theorem fast_strict (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n)
    (a : Tree) (n : Nat) : n + 1 ≤ fast b a n :=
  Nat.le_trans (hb n)
    (base_le_fast b (fun m => Nat.le_trans (Nat.le_succ m) (hb m)) a n)

theorem fast_succ_gain (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n)
    (a : Tree) (n : Nat) : fast b a n + n ≤ fast b (.succ a) n :=
  iterate_add_le (fast_strict b hb a) n (fast b a n)

theorem fast_at_zero (b : Nat → Nat) (a : Tree) : fast b a 0 = b 0 := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih
  | limit f ih => exact ih 0

/-- Exact substitution law, proved pointwise without function extensionality. -/
theorem fast_graft (b : Nat → Nat) (a t : Tree) (n : Nat) :
    fast b (graft a t) n = fast (fast b a) t n := by
  induction t generalizing n with
  | zero => rfl
  | succ t ih => exact iterate_congr ih (n + 1) n
  | limit f ih => exact ih n n

theorem graft_lower (b : Nat → Nat) (hb : ∀ n, n ≤ b n)
    (a t : Tree) (n : Nat) : fast b a n ≤ fast b (graft a t) n := by
  rw [fast_graft]
  exact base_le_fast (fast b a) (fast_inflationary b hb a) t n

theorem advance_gain (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n)
    (a : Tree) (n : Nat) : fast b a n + n ≤ fast b (advance b a) n := by
  exact Nat.le_trans (fast_succ_gain b hb a n)
    (graft_lower b (fun m => Nat.le_trans (Nat.le_succ m) (hb m))
      (.succ a) _ n)

theorem iteration_gain {α : Type u} (score : α → Nat) (f : α → α)
    (d : Nat) (h : ∀ x, score x + d ≤ score (f x)) (k : Nat) (a : α) :
    score a + k * d ≤ score (iterate f k a) := by
  induction k generalizing a with
  | zero =>
      rw [Nat.zero_mul, Nat.add_zero]
      exact Nat.le_refl (score a)
  | succ k ih =>
      calc
        score a + (k + 1) * d = (score a + d) + k * d := by
          rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (k * d) d,
            ← Nat.add_assoc]
        _ ≤ score (f a) + k * d := Nat.add_le_add_right (h a) (k * d)
        _ ≤ score (iterate f k (f a)) := ih (f a)

theorem tower2_lower (n : Nat) : n + 1 ≤ tower2 n := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ n ih =>
      exact Nat.le_trans (Nat.add_le_add_right ih 1)
        (Nat.lt_pow_self (n := tower2 n) (by decide : 1 < 2))

theorem tower2_step (n : Nat) : tower2 n ≤ tower2 (n + 1) :=
  Nat.le_of_lt (Nat.lt_pow_self (n := tower2 n) (by decide : 1 < 2))

theorem tower2_mono {m n : Nat} (h : m ≤ n) : tower2 m ≤ tower2 n := by
  induction h with
  | refl => exact Nat.le_refl (tower2 m)
  | @step n h ih => exact Nat.le_trans ih (tower2_step n)

theorem stage_raw_gain (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n) (a : Tree) :
    fast b a 64 + tower2 (fast b a 64 + 1) * 64 ≤ fast b (stage b a) 64 :=
  iteration_gain (fun t => fast b t 64) (advance b) 64
    (fun t => advance_gain b hb t 64) (tower2 (fast b a 64 + 1)) a

theorem stage_gain (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n) (a : Tree) :
    fast b a 64 + (fast b a 64 + 1) * 64 ≤ fast b (stage b a) 64 := by
  have hcount : fast b a 64 + 1 ≤ tower2 (fast b a 64 + 1) :=
    Nat.le_trans (Nat.le_succ (fast b a 64 + 1)) (tower2_lower _)
  exact Nat.le_trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right 64 hcount) (fast b a 64))
    (stage_raw_gain b hb a)

theorem stage_tower (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n) (a : Tree) :
    tower2 (fast b a 64 + 1) ≤ fast b (stage b a) 64 := by
  have hmul : tower2 (fast b a 64 + 1) ≤ tower2 (fast b a 64 + 1) * 64 := by
    calc
      tower2 (fast b a 64 + 1) = tower2 (fast b a 64 + 1) * 1 :=
        (Nat.mul_one _).symm
      _ ≤ tower2 (fast b a 64 + 1) * 64 :=
        Nat.mul_le_mul_left _ (by decide : 1 ≤ 64)
  exact Nat.le_trans hmul
    (Nat.le_trans (Nat.le_add_left _ _) (stage_raw_gain b hb a))

theorem scale_identity (m : Nat) :
    65 * (m + 1) = (m + (m + 1) * 64) + 1 := by
  change (64 + 1) * (m + 1) = (m + (m + 1) * 64) + 1
  rw [Nat.succ_mul, Nat.mul_comm 64 (m + 1), ← Nat.add_assoc,
    Nat.add_comm ((m + 1) * 64) m]

theorem stage_scale (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n) (a : Tree) :
    65 * (fast b a 64 + 1) ≤ fast b (stage b a) 64 + 1 := by
  rw [scale_identity]
  exact Nat.add_le_add_right (stage_gain b hb a) 1

/-- The library's associativity lemma carries `propext`; this proof does not. -/
theorem mul_assoc_pure (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
      calc
        (a * b) * (c + 1) = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * (c + 1)) := congrArg (Nat.mul a) (Nat.mul_succ b c).symm

theorem ladder_scale (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n) (k : Nat) :
    65 ^ k * (seedScore b + 1) ≤ fast b (ladder b k) 64 + 1 := by
  induction k with
  | zero =>
      rw [Nat.pow_zero, Nat.one_mul]
      exact Nat.le_refl (seedScore b + 1)
  | succ k ih =>
      calc
        65 ^ (k + 1) * (seedScore b + 1) =
            65 * (65 ^ k * (seedScore b + 1)) := by
          rw [Nat.pow_succ, Nat.mul_comm (65 ^ k) 65, mul_assoc_pure]
        _ ≤ 65 * (fast b (ladder b k) 64 + 1) := Nat.mul_le_mul_left 65 ih
        _ ≤ fast b (stage b (ladder b k)) 64 + 1 :=
          stage_scale b hb (ladder b k)

theorem candidate_bound (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n) :
    65 ^ (seedScore b) * (seedScore b + 1) ≤ candidate b + 1 :=
  ladder_scale b hb (seedScore b)

theorem ladder_tower (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n) (k : Nat) :
    towerFeedback (seedScore b) k ≤ fast b (ladder b k) 64 := by
  induction k with
  | zero => exact Nat.le_refl (seedScore b)
  | succ k ih =>
      exact Nat.le_trans (tower2_mono (Nat.add_le_add_right ih 1))
        (stage_tower b hb (ladder b k))

theorem candidate_tower (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n) :
    towerFeedback (seedScore b) (seedScore b) ≤ candidate b :=
  ladder_tower b hb (seedScore b)

theorem towerFeedback_seed_mono {s t : Nat} (h : s ≤ t) (k : Nat) :
    towerFeedback s k ≤ towerFeedback t k := by
  induction k with
  | zero => exact h
  | succ k ih => exact tower2_mono (Nat.add_le_add_right ih 1)

theorem towerFeedback_step (s k : Nat) :
    towerFeedback s k ≤ towerFeedback s (k + 1) :=
  Nat.le_trans (Nat.le_add_right (towerFeedback s k) 2)
    (tower2_lower (towerFeedback s k + 1))

theorem towerFeedback_rounds_mono (s : Nat) {k l : Nat} (h : k ≤ l) :
    towerFeedback s k ≤ towerFeedback s l := by
  induction h with
  | refl => exact Nat.le_refl (towerFeedback s k)
  | @step l h ih => exact Nat.le_trans ih (towerFeedback_step s l)

theorem towerFeedback_diagonal_mono {s t : Nat} (h : s ≤ t) :
    towerFeedback s s ≤ towerFeedback t t :=
  Nat.le_trans (towerFeedback_seed_mono h s) (towerFeedback_rounds_mono t h)

theorem candidate_tower_from (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n)
    (c : Nat) (hc : c ≤ seedScore b) : towerFeedback c c ≤ candidate b :=
  Nat.le_trans (towerFeedback_diagonal_mono hc) (candidate_tower b hb)

theorem base_le_candidate (b : Nat → Nat) (hb : ∀ n, n ≤ b n) :
    b 64 ≤ candidate b := base_le_fast b hb (ladder b (seedScore b)) 64

end BigNumber.Amplifier
