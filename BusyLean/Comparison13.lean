import BusyLean.Contender13
import BusyLean.Comparison12

/-! # Contender 13: comparison theorems -/

namespace BusyLean.Fd

theorem lt_reflectFd {f : Nat → Nat} {n m : Nat}
    (h : m ≤ BigNumber.maxN (f n) (BigNumber.maximum (fvalue f n) (ctmsUpTo n))) :
    m < reflectFd f n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectFd (f : Nat → Nat) (n : Nat) : f n < reflectFd f n :=
  lt_reflectFd (BigNumber.le_maxN_left _ _)

theorem fvalue_lt_reflectFd (f : Nat → Nat) {n : Nat} {t : CTm} (ht : t ∈ ctmsUpTo n) :
    fvalue f n t < reflectFd f n :=
  lt_reflectFd (Nat.le_trans (W.le_maximum (fvalue f n) ht) (BigNumber.le_maxN_right _ _))

theorem input_lt_reflectFd (f : Nat → Nat) (n : Nat) : n < reflectFd f n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

end BusyLean.Fd

namespace BusyLean

/-- At every input, `F13` exceeds Contender 12's family. -/
theorem family12_lt_F13 (n : Nat) : family12 n < F13 n := Fd.oracle_lt_reflectFd family12 n

/-- **The required comparison**: Contender 12 is strictly smaller than Contender 13. -/
theorem contender_12_lt_contender_13 : contender_12 < contender_13 :=
  Nat.lt_trans (family12_lt_F13 42) (Fd.input_lt_reflectFd family12 (F13 42))

theorem contender_11_lt_contender_13 : contender_11 < contender_13 :=
  Nat.lt_trans contender_11_lt_contender_12 contender_12_lt_contender_13

/-- Every dynamic-kind program of depth `≤ F13 42` is exceeded by Contender 13. -/
theorem fvalue_lt_contender_13 {t : Fd.CTm} (ht : t ∈ Fd.ctmsUpTo (F13 42)) :
    Fd.fvalue family12 (F13 42) t < contender_13 :=
  Fd.fvalue_lt_reflectFd family12 ht

end BusyLean
