import BusyLean.Contender8
import BusyLean.Comparison7

/-! # Contender 8: comparison theorems -/

namespace BusyLean.Fw

theorem lt_reflectFw {f : Nat → Nat} {n m : Nat}
    (h : m ≤ BigNumber.maxN (f n) (BigNumber.maximum (fvalue f n) (ctmsUpTo n))) :
    m < reflectFw f n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectFw (f : Nat → Nat) (n : Nat) : f n < reflectFw f n :=
  lt_reflectFw (BigNumber.le_maxN_left _ _)

theorem fvalue_lt_reflectFw (f : Nat → Nat) {n : Nat} {t : CTm} (ht : t ∈ ctmsUpTo n) :
    fvalue f n t < reflectFw f n :=
  lt_reflectFw (Nat.le_trans (W.le_maximum (fvalue f n) ht) (BigNumber.le_maxN_right _ _))

theorem input_lt_reflectFw (f : Nat → Nat) (n : Nat) : n < reflectFw f n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

end BusyLean.Fw

namespace BusyLean

/-- At every input, `F8` exceeds Contender 7's family. -/
theorem family7_lt_F8 (n : Nat) : family7 n < F8 n := Fw.oracle_lt_reflectFw family7 n

/-- **The required comparison**: Contender 7 is strictly smaller than Contender 8. -/
theorem contender_7_lt_contender_8 : contender_7 < contender_8 :=
  Nat.lt_trans (family7_lt_F8 42) (Fw.input_lt_reflectFw family7 (F8 42))

theorem contender_6_lt_contender_8 : contender_6 < contender_8 :=
  Nat.lt_trans contender_6_lt_contender_7 contender_7_lt_contender_8

/-- Every Fω program of depth `≤ F8 42` is exceeded by Contender 8. -/
theorem fvalue_lt_contender_8 {t : Fw.CTm} (ht : t ∈ Fw.ctmsUpTo (F8 42)) :
    Fw.fvalue family7 (F8 42) t < contender_8 :=
  Fw.fvalue_lt_reflectFw family7 ht

end BusyLean
