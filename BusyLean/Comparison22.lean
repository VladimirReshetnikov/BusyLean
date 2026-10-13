import BusyLean.Contender22
import BusyLean.Comparison21

/-! # Contender 22: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectTwFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.tvalue22 n (packFamily fs) n) (FL.towerLadderUpTo n))) :
    m < reflectTwFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectTwFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectTwFamily fs n :=
  lt_reflectTwFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem tvalue22_lt_reflectTwFamily (fs : Family) {n : Nat} {t : FL.CTm ((Ordinal.tower n).T)}
    (ht : t ∈ FL.towerLadderUpTo n) :
    FL.tvalue22 n (packFamily fs) n t < reflectTwFamily fs n :=
  lt_reflectTwFamily
    (Nat.le_trans (le_maximum (FL.tvalue22 n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem twTransformer_progressive : Progressive twTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectTwFamily seed hi

/-- At every input, `F22` exceeds Contender 21's family. -/
theorem family21_lt_F22 (n : Nat) : family21 n < F22 n :=
  ((diagonalLift_preservesProgressive (schedule22 n) (rank22 n))
    twTransformer twTransformer_progressive)
    (fun _ => family21) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F22 (n : Nat) : reflectTwFamily (fun _ => family21) n < F22 n :=
  (diagonalLift_strictlyInflationary (schedule22 n) (rank22 n))
    twTransformer twTransformer_progressive (fun _ => family21) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the atoms of `tower n`, run with the packed seed,
is below `F22 n`. -/
theorem tvalue22_lt_F22 {n : Nat} {t : FL.CTm ((Ordinal.tower n).T)} (ht : t ∈ FL.towerLadderUpTo n) :
    FL.tvalue22 n (packFamily (fun _ => family21)) n t < F22 n :=
  Nat.lt_trans (tvalue22_lt_reflectTwFamily (fun _ => family21) ht) (raw_reflection_lt_F22 n)

theorem input_lt_family21 (n : Nat) : n < family21 n :=
  Nat.lt_trans (input_lt_F21 n) (input_lt_F21 (F21 n))

theorem input_lt_F22 (n : Nat) : n < F22 n :=
  Nat.lt_trans (input_lt_family21 n) (family21_lt_F22 n)

/-- **The required comparison**: Contender 21 is strictly smaller than Contender 22. -/
theorem contender_21_lt_contender_22 : contender_21 < contender_22 :=
  Nat.lt_trans (family21_lt_F22 42) (input_lt_F22 (F22 42))

theorem contender_20_lt_contender_22 : contender_20 < contender_22 :=
  Nat.lt_trans contender_20_lt_contender_21 contender_21_lt_contender_22

end BusyLean
