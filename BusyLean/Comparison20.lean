import BusyLean.Contender20
import BusyLean.Comparison19

/-! # Contender 20: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectBFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.bvalue (packFamily fs) n) (FL.bhLadderUpTo n))) :
    m < reflectBFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectBFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectBFamily fs n :=
  lt_reflectBFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem bvalue_lt_reflectBFamily (fs : Family) {n : Nat} {t : FL.CTm Ordinal.BachmannHoward}
    (ht : t ∈ FL.bhLadderUpTo n) :
    FL.bvalue (packFamily fs) n t < reflectBFamily fs n :=
  lt_reflectBFamily
    (Nat.le_trans (le_maximum (FL.bvalue (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem bTransformer_progressive : Progressive bTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectBFamily seed hi

/-- At every input, `F20` exceeds Contender 19's family. -/
theorem family19_lt_F20 (n : Nat) : family19 n < F20 n :=
  ((diagonalLift_preservesProgressive (schedule20 n) (rank20 n))
    bTransformer bTransformer_progressive)
    (fun _ => family19) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F20 (n : Nat) : reflectBFamily (fun _ => family19) n < F20 n :=
  (diagonalLift_strictlyInflationary (schedule20 n) (rank20 n))
    bTransformer bTransformer_progressive (fun _ => family19) n n n (Nat.le_refl n)

/-- Every Bachmann–Howard-ladder program of depth `≤ n`, run with the packed seed,
is below `F20 n`. -/
theorem bvalue_lt_F20 {n : Nat} {t : FL.CTm Ordinal.BachmannHoward} (ht : t ∈ FL.bhLadderUpTo n) :
    FL.bvalue (packFamily (fun _ => family19)) n t < F20 n :=
  Nat.lt_trans (bvalue_lt_reflectBFamily (fun _ => family19) ht) (raw_reflection_lt_F20 n)

theorem input_lt_family19 (n : Nat) : n < family19 n :=
  Nat.lt_trans (input_lt_F19 n) (input_lt_F19 (F19 n))

theorem input_lt_F20 (n : Nat) : n < F20 n :=
  Nat.lt_trans (input_lt_family19 n) (family19_lt_F20 n)

/-- **The required comparison**: Contender 19 is strictly smaller than Contender 20. -/
theorem contender_19_lt_contender_20 : contender_19 < contender_20 :=
  Nat.lt_trans (family19_lt_F20 42) (input_lt_F20 (F20 42))

theorem contender_18_lt_contender_20 : contender_18 < contender_20 :=
  Nat.lt_trans contender_18_lt_contender_19 contender_19_lt_contender_20

end BusyLean
