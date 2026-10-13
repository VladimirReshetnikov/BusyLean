import BusyLean.Contender24
import BusyLean.Comparison23

/-! # Contender 24: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectRFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.rvalue n (packFamily fs) n) (FL.roundLadderUpTo n))) :
    m < reflectRFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectRFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectRFamily fs n :=
  lt_reflectRFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem rvalue_lt_reflectRFamily (fs : Family) {n : Nat} {t : FL.CTm ((Ordinal.roundTower n).T)}
    (ht : t ∈ FL.roundLadderUpTo n) :
    FL.rvalue n (packFamily fs) n t < reflectRFamily fs n :=
  lt_reflectRFamily
    (Nat.le_trans (le_maximum (FL.rvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem rTransformer_progressive : Progressive rTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectRFamily seed hi

/-- At every input, `F24` exceeds Contender 23's family. -/
theorem family23_lt_F24 (n : Nat) : family23 n < F24 n :=
  ((wDiagonalLift_preservesProgressive (schedule24 n) (rank24 n))
    rTransformer rTransformer_progressive)
    (fun _ => family23) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F24 (n : Nat) : reflectRFamily (fun _ => family23) n < F24 n :=
  (wDiagonalLift_strictlyInflationary (schedule24 n) (rank24 n))
    rTransformer rTransformer_progressive (fun _ => family23) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the atoms of `roundTower n`, run with the
packed seed, is below `F24 n`. -/
theorem rvalue_lt_F24 {n : Nat} {t : FL.CTm ((Ordinal.roundTower n).T)}
    (ht : t ∈ FL.roundLadderUpTo n) :
    FL.rvalue n (packFamily (fun _ => family23)) n t < F24 n :=
  Nat.lt_trans (rvalue_lt_reflectRFamily (fun _ => family23) ht) (raw_reflection_lt_F24 n)

theorem input_lt_family23 (n : Nat) : n < family23 n :=
  Nat.lt_trans (input_lt_F23 n) (input_lt_F23 (F23 n))

theorem input_lt_F24 (n : Nat) : n < F24 n :=
  Nat.lt_trans (input_lt_family23 n) (family23_lt_F24 n)

/-- **The required comparison**: Contender 23 is strictly smaller than Contender 24. -/
theorem contender_23_lt_contender_24 : contender_23 < contender_24 :=
  Nat.lt_trans (family23_lt_F24 42) (input_lt_F24 (F24 42))

theorem contender_22_lt_contender_24 : contender_22 < contender_24 :=
  Nat.lt_trans contender_22_lt_contender_23 contender_23_lt_contender_24

end BusyLean
