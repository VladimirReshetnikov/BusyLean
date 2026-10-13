import BusyLean.Contender18
import BusyLean.Comparison17

/-! # Contender 18: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectGFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.gvalue (packFamily fs) n) (FL.gamma0LadderUpTo n))) :
    m < reflectGFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectGFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectGFamily fs n :=
  lt_reflectGFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem gvalue_lt_reflectGFamily (fs : Family) {n : Nat} {t : FL.CTm Ordinal.Gamma0}
    (ht : t ∈ FL.gamma0LadderUpTo n) :
    FL.gvalue (packFamily fs) n t < reflectGFamily fs n :=
  lt_reflectGFamily
    (Nat.le_trans (le_maximum (FL.gvalue (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem gTransformer_progressive : Progressive gTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectGFamily seed hi

/-- At every input, `F18` exceeds Contender 17's family. -/
theorem family17_lt_F18 (n : Nat) : family17 n < F18 n :=
  ((diagonalLift_preservesProgressive (schedule18 n) (rank18 n))
    gTransformer gTransformer_progressive)
    (fun _ => family17) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F18 (n : Nat) : reflectGFamily (fun _ => family17) n < F18 n :=
  (diagonalLift_strictlyInflationary (schedule18 n) (rank18 n))
    gTransformer gTransformer_progressive (fun _ => family17) n n n (Nat.le_refl n)

/-- Every Γ₀-ladder program of depth `≤ n`, run with the packed seed,
is below `F18 n`. -/
theorem gvalue_lt_F18 {n : Nat} {t : FL.CTm Ordinal.Gamma0} (ht : t ∈ FL.gamma0LadderUpTo n) :
    FL.gvalue (packFamily (fun _ => family17)) n t < F18 n :=
  Nat.lt_trans (gvalue_lt_reflectGFamily (fun _ => family17) ht) (raw_reflection_lt_F18 n)

theorem input_lt_family17 (n : Nat) : n < family17 n :=
  Nat.lt_trans (input_lt_F17 n) (input_lt_F17 (F17 n))

theorem input_lt_F18 (n : Nat) : n < F18 n :=
  Nat.lt_trans (input_lt_family17 n) (family17_lt_F18 n)

/-- **The required comparison**: Contender 17 is strictly smaller than Contender 18. -/
theorem contender_17_lt_contender_18 : contender_17 < contender_18 :=
  Nat.lt_trans (family17_lt_F18 42) (input_lt_F18 (F18 42))

theorem contender_16_lt_contender_18 : contender_16 < contender_18 :=
  Nat.lt_trans contender_16_lt_contender_17 contender_17_lt_contender_18

end BusyLean
