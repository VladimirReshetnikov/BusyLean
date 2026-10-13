import BusyLean.Contender16
import BusyLean.Comparison15

/-! # Contender 16: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectTFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.tvalue (packFamily fs) n) (FL.transfiniteUpTo n))) :
    m < reflectTFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectTFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectTFamily fs n :=
  lt_reflectTFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem tvalue_lt_reflectTFamily (fs : Family) {n : Nat} {t : FL.CTm Ordinal.OmegaPow}
    (ht : t ∈ FL.transfiniteUpTo n) :
    FL.tvalue (packFamily fs) n t < reflectTFamily fs n :=
  lt_reflectTFamily
    (Nat.le_trans (le_maximum (FL.tvalue (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem tTransformer_progressive : Progressive tTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectTFamily seed hi

/-- At every input, `F16` exceeds Contender 15's family. -/
theorem family15_lt_F16 (n : Nat) : family15 n < F16 n :=
  ((diagonalLift_preservesProgressive (schedule16 n) (rank16 n))
    tTransformer tTransformer_progressive)
    (fun _ => family15) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F16 (n : Nat) : reflectTFamily (fun _ => family15) n < F16 n :=
  (diagonalLift_strictlyInflationary (schedule16 n) (rank16 n))
    tTransformer tTransformer_progressive (fun _ => family15) n n n (Nat.le_refl n)

/-- Every transfinite-ladder program of depth `≤ n`, run with the packed seed,
is below `F16 n`. -/
theorem tvalue_lt_F16 {n : Nat} {t : FL.CTm Ordinal.OmegaPow} (ht : t ∈ FL.transfiniteUpTo n) :
    FL.tvalue (packFamily (fun _ => family15)) n t < F16 n :=
  Nat.lt_trans (tvalue_lt_reflectTFamily (fun _ => family15) ht) (raw_reflection_lt_F16 n)

theorem input_lt_family15 (n : Nat) : n < family15 n :=
  Nat.lt_trans (input_lt_F15 n) (input_lt_F15 (F15 n))

theorem input_lt_F16 (n : Nat) : n < F16 n :=
  Nat.lt_trans (input_lt_family15 n) (family15_lt_F16 n)

/-- **The required comparison**: Contender 15 is strictly smaller than Contender 16. -/
theorem contender_15_lt_contender_16 : contender_15 < contender_16 :=
  Nat.lt_trans (family15_lt_F16 42) (input_lt_F16 (F16 42))

theorem contender_14_lt_contender_16 : contender_14 < contender_16 :=
  Nat.lt_trans contender_14_lt_contender_15 contender_15_lt_contender_16

end BusyLean
