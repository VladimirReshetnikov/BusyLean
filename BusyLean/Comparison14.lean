import BusyLean.Contender14
import BusyLean.Comparison13

/-! # Contender 14: comparison theorems -/

namespace BusyLean.FL

theorem lt_reflectFL {f : Nat → Nat} {n m : Nat}
    (h : m ≤ BigNumber.maxN (f n) (BigNumber.maximum (fvalue n f n) (ladderUpTo n))) :
    m < reflectFL f n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectFL (f : Nat → Nat) (n : Nat) : f n < reflectFL f n :=
  lt_reflectFL (BigNumber.le_maxN_left _ _)

theorem fvalue_lt_reflectFL (f : Nat → Nat) {n : Nat} {t : CTm (Atom n)}
    (ht : t ∈ ladderUpTo n) : fvalue n f n t < reflectFL f n :=
  lt_reflectFL (Nat.le_trans (W.le_maximum (fvalue n f n) ht) (BigNumber.le_maxN_right _ _))

theorem input_lt_reflectFL (f : Nat → Nat) (n : Nat) : n < reflectFL f n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

end BusyLean.FL

namespace BusyLean

/-- At every input, `F14` exceeds Contender 13's family. -/
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n := FL.oracle_lt_reflectFL family13 n

/-- **The required comparison**: Contender 13 is strictly smaller than Contender 14. -/
theorem contender_13_lt_contender_14 : contender_13 < contender_14 :=
  Nat.lt_trans (family13_lt_F14 42) (FL.input_lt_reflectFL family13 (F14 42))

theorem contender_12_lt_contender_14 : contender_12 < contender_14 :=
  Nat.lt_trans contender_12_lt_contender_13 contender_13_lt_contender_14

/-- Every level-`F14 42` ladder program of depth `≤ F14 42` is exceeded by Contender 14. -/
theorem fvalue_lt_contender_14 {t : FL.CTm (FL.Atom (F14 42))} (ht : t ∈ FL.ladderUpTo (F14 42)) :
    FL.fvalue (F14 42) family13 (F14 42) t < contender_14 :=
  FL.fvalue_lt_reflectFL family13 ht

end BusyLean
