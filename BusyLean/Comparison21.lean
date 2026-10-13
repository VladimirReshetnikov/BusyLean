import BusyLean.Contender21
import BusyLean.Comparison20

/-! # Contender 21: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectZFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.zvalue n (packFamily fs) n) (FL.buchholzLadderUpTo n))) :
    m < reflectZFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectZFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectZFamily fs n :=
  lt_reflectZFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem zvalue_lt_reflectZFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Buchholz n)}
    (ht : t ∈ FL.buchholzLadderUpTo n) :
    FL.zvalue n (packFamily fs) n t < reflectZFamily fs n :=
  lt_reflectZFamily
    (Nat.le_trans (le_maximum (FL.zvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem zTransformer_progressive : Progressive zTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectZFamily seed hi

/-- At every input, `F21` exceeds Contender 20's family. -/
theorem family20_lt_F21 (n : Nat) : family20 n < F21 n :=
  ((diagonalLift_preservesProgressive (schedule21 n) (rank21 n))
    zTransformer zTransformer_progressive)
    (fun _ => family20) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F21 (n : Nat) : reflectZFamily (fun _ => family20) n < F21 n :=
  (diagonalLift_strictlyInflationary (schedule21 n) (rank21 n))
    zTransformer zTransformer_progressive (fun _ => family20) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the level-`n` Buchholz atoms, run with the packed seed,
is below `F21 n`. -/
theorem zvalue_lt_F21 {n : Nat} {t : FL.CTm (Ordinal.Buchholz n)} (ht : t ∈ FL.buchholzLadderUpTo n) :
    FL.zvalue n (packFamily (fun _ => family20)) n t < F21 n :=
  Nat.lt_trans (zvalue_lt_reflectZFamily (fun _ => family20) ht) (raw_reflection_lt_F21 n)

theorem input_lt_family20 (n : Nat) : n < family20 n :=
  Nat.lt_trans (input_lt_F20 n) (input_lt_F20 (F20 n))

theorem input_lt_F21 (n : Nat) : n < F21 n :=
  Nat.lt_trans (input_lt_family20 n) (family20_lt_F21 n)

/-- **The required comparison**: Contender 20 is strictly smaller than Contender 21. -/
theorem contender_20_lt_contender_21 : contender_20 < contender_21 :=
  Nat.lt_trans (family20_lt_F21 42) (input_lt_F21 (F21 42))

theorem contender_19_lt_contender_21 : contender_19 < contender_21 :=
  Nat.lt_trans contender_19_lt_contender_20 contender_20_lt_contender_21

end BusyLean
