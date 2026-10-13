import BusyLean.Contender7
import BusyLean.Comparison

/-! # Contender 7: comparison theorems -/

namespace BusyLean.F

theorem lt_reflectF {f : Nat → Nat} {n m : Nat}
    (h : m ≤ BigNumber.maxN (f n) (BigNumber.maximum (fvalue f) (ctmsUpTo n))) :
    m < reflectF f n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- The oracle is exceeded. -/
theorem oracle_lt_reflectF (f : Nat → Nat) (n : Nat) : f n < reflectF f n :=
  lt_reflectF (BigNumber.le_maxN_left _ _)

/-- Every enumerated System F program is exceeded. -/
theorem fvalue_lt_reflectF (f : Nat → Nat) {n : Nat} {t : CTm} (ht : t ∈ ctmsUpTo n) :
    fvalue f t < reflectF f n :=
  lt_reflectF (Nat.le_trans (W.le_maximum (fvalue f) ht) (BigNumber.le_maxN_right _ _))

/-- The input is exceeded. -/
theorem input_lt_reflectF (f : Nat → Nat) (n : Nat) : n < reflectF f n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

end BusyLean.F

namespace BusyLean

/-- At every input, `F7` exceeds Contender 6's family. -/
theorem finalFamily_lt_F7 (n : Nat) : finalFamily n < F7 n :=
  F.oracle_lt_reflectF finalFamily n

/-- **The required comparison**: Contender 6 is strictly smaller than Contender 7. -/
theorem contender_6_lt_contender_7 : contender_6 < contender_7 :=
  Nat.lt_trans (finalFamily_lt_F7 42) (F.input_lt_reflectF finalFamily (F7 42))

/-- Every System F program of depth `≤ F7 42` is exceeded by Contender 7: the
outer reflection runs System F at a syntax budget larger than Contender 6. -/
theorem fvalue_lt_contender_7 {t : F.CTm} (ht : t ∈ F.ctmsUpTo (F7 42)) :
    F.fvalue finalFamily t < contender_7 :=
  F.fvalue_lt_reflectF finalFamily ht

theorem contender_5_lt_contender_7 : contender_5 < contender_7 :=
  Nat.lt_trans contender_5_lt_contender_6 contender_6_lt_contender_7

end BusyLean
