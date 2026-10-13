import BusyLean.Contender10
import BusyLean.Comparison9

/-! # Contender 10: comparison theorems -/

namespace BusyLean.Fk

theorem lt_reflectFk {f : Nat → Nat} {n m : Nat}
    (h : m ≤ BigNumber.maxN (f n) (BigNumber.maximum (fvalue f n) (ctmsUpTo n))) :
    m < reflectFk f n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectFk (f : Nat → Nat) (n : Nat) : f n < reflectFk f n :=
  lt_reflectFk (BigNumber.le_maxN_left _ _)

theorem fvalue_lt_reflectFk (f : Nat → Nat) {n : Nat} {t : CTm} (ht : t ∈ ctmsUpTo n) :
    fvalue f n t < reflectFk f n :=
  lt_reflectFk (Nat.le_trans (W.le_maximum (fvalue f n) ht) (BigNumber.le_maxN_right _ _))

theorem input_lt_reflectFk (f : Nat → Nat) (n : Nat) : n < reflectFk f n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

end BusyLean.Fk

namespace BusyLean

/-- At every input, `F10` exceeds Contender 9's family. -/
theorem family9_lt_F10 (n : Nat) : family9 n < F10 n := Fk.oracle_lt_reflectFk family9 n

/-- **The required comparison**: Contender 9 is strictly smaller than Contender 10. -/
theorem contender_9_lt_contender_10 : contender_9 < contender_10 :=
  Nat.lt_trans (family9_lt_F10 42) (Fk.input_lt_reflectFk family9 (F10 42))

theorem contender_8_lt_contender_10 : contender_8 < contender_10 :=
  Nat.lt_trans contender_8_lt_contender_9 contender_9_lt_contender_10

/-- Every kind-polymorphic program of depth `≤ F10 42` is exceeded by Contender 10. -/
theorem fvalue_lt_contender_10 {t : Fk.CTm} (ht : t ∈ Fk.ctmsUpTo (F10 42)) :
    Fk.fvalue family9 (F10 42) t < contender_10 :=
  Fk.fvalue_lt_reflectFk family9 ht

end BusyLean
