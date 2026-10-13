import BigNumber.BaseDefs
import BigNumber.Baseline

namespace BigNumber

theorem envelope_le_prefix (n : Nat) :
    Baseline.envelope n ≤ prefixEnvelope n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_add_left _ _

theorem prefix_mono {n m : Nat} (h : n ≤ m) :
    prefixEnvelope n ≤ prefixEnvelope m := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step m h ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem base_inflationary (n : Nat) : n < base n :=
  Nat.lt_of_le_of_lt (Nat.le_add_left n (prefixEnvelope n))
    (Nat.lt_succ_self _)

theorem prefix_lt_base (n : Nat) : prefixEnvelope n < base n :=
  Nat.lt_of_le_of_lt (Nat.le_add_right (prefixEnvelope n) n)
    (Nat.lt_succ_self _)

theorem envelope_lt_base {k n : Nat} (h : k ≤ n) :
    Baseline.envelope k < base n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (envelope_le_prefix k) (prefix_mono h))
    (prefix_lt_base n)

theorem contender_5_lt_base64 : Baseline.contender_5 < base 64 := by
  rw [Baseline.contender_5_eq_envelope]
  exact envelope_lt_base (by decide)

end BigNumber
