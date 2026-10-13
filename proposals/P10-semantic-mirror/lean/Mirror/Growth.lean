import Mirror.Model
import Lean

namespace BusyLean.Mirror

theorem self_lt_pow2 (n : Nat) : n < BigNumber.pow2 n := by
  induction n with
  | zero => decide
  | succ n ih =>
      change n + 1 < 2 * BigNumber.pow2 n
      omega

private theorem pow2_le_next (n : Nat) :
    BigNumber.pow2 n ≤ BigNumber.pow2 (n + 1) := by
  change BigNumber.pow2 n ≤ 2 * BigNumber.pow2 n
  omega

theorem pow2_mono {a b : Nat} (h : a ≤ b) :
    BigNumber.pow2 a ≤ BigNumber.pow2 b := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step b h ih => exact Nat.le_trans ih (pow2_le_next b)

theorem tower_input_mono (h : Nat) {a b : Nat} (hab : a ≤ b) :
    tower h a ≤ tower h b := by
  induction h with
  | zero => exact hab
  | succ h ih => exact pow2_mono ih

theorem tower_le_next (h x : Nat) : tower h x ≤ tower (h + 1) x :=
  Nat.le_of_lt (self_lt_pow2 (tower h x))

theorem tower_height_mono {h k : Nat} (hhk : h ≤ k) (x : Nat) :
    tower h x ≤ tower k x := by
  induction hhk with
  | refl => exact Nat.le_refl _
  | @step k hhk ih => exact Nat.le_trans ih (tower_le_next k x)

theorem self_lt_boost (x : Nat) : x < boost x := by
  unfold boost
  omega

theorem boost_mono {a b : Nat} (h : a ≤ b) : boost a ≤ boost b := by
  have h1 := tower_input_mono (a + 1) (Nat.succ_le_succ h)
  have h2 := tower_height_mono (Nat.succ_le_succ h) (b + 1)
  have ht := Nat.le_trans h1 h2
  unfold boost
  omega

theorem self_le_boostIter (k x : Nat) : x ≤ boostIter k x := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (self_lt_boost (boostIter k x)))

end BusyLean.Mirror
