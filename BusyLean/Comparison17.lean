import BusyLean.Contender17
import BusyLean.Comparison16

/-! # Contender 17: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectEFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.evalue (packFamily fs) n) (FL.epsilon0LadderUpTo n))) :
    m < reflectEFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectEFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectEFamily fs n :=
  lt_reflectEFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem evalue_lt_reflectEFamily (fs : Family) {n : Nat} {t : FL.CTm Ordinal.Epsilon0}
    (ht : t ∈ FL.epsilon0LadderUpTo n) :
    FL.evalue (packFamily fs) n t < reflectEFamily fs n :=
  lt_reflectEFamily
    (Nat.le_trans (le_maximum (FL.evalue (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem eTransformer_progressive : Progressive eTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectEFamily seed hi

/-- At every input, `F17` exceeds Contender 16's family. -/
theorem family16_lt_F17 (n : Nat) : family16 n < F17 n :=
  ((diagonalLift_preservesProgressive (schedule17 n) (rank17 n))
    eTransformer eTransformer_progressive)
    (fun _ => family16) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F17 (n : Nat) : reflectEFamily (fun _ => family16) n < F17 n :=
  (diagonalLift_strictlyInflationary (schedule17 n) (rank17 n))
    eTransformer eTransformer_progressive (fun _ => family16) n n n (Nat.le_refl n)

/-- Every ε₀-ladder program of depth `≤ n`, run with the packed seed,
is below `F17 n`. -/
theorem evalue_lt_F17 {n : Nat} {t : FL.CTm Ordinal.Epsilon0} (ht : t ∈ FL.epsilon0LadderUpTo n) :
    FL.evalue (packFamily (fun _ => family16)) n t < F17 n :=
  Nat.lt_trans (evalue_lt_reflectEFamily (fun _ => family16) ht) (raw_reflection_lt_F17 n)

theorem input_lt_family16 (n : Nat) : n < family16 n :=
  Nat.lt_trans (input_lt_F16 n) (input_lt_F16 (F16 n))

theorem input_lt_F17 (n : Nat) : n < F17 n :=
  Nat.lt_trans (input_lt_family16 n) (family16_lt_F17 n)

/-- **The required comparison**: Contender 16 is strictly smaller than Contender 17. -/
theorem contender_16_lt_contender_17 : contender_16 < contender_17 :=
  Nat.lt_trans (family16_lt_F17 42) (input_lt_F17 (F17 42))

theorem contender_15_lt_contender_17 : contender_15 < contender_17 :=
  Nat.lt_trans contender_15_lt_contender_16 contender_16_lt_contender_17

end BusyLean
