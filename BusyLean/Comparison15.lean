import BusyLean.Contender15
import BusyLean.HyperReflectionFacts
import BusyLean.Comparison14

/-! # Contender 15: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectFLFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.fvalue n (packFamily fs) n) (FL.ladderUpTo n))) :
    m < reflectFLFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectFLFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectFLFamily fs n :=
  lt_reflectFLFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem fvalue_lt_reflectFLFamily (fs : Family) {n : Nat} {t : FL.CTm (FL.Atom n)}
    (ht : t ∈ FL.ladderUpTo n) :
    FL.fvalue n (packFamily fs) n t < reflectFLFamily fs n :=
  lt_reflectFLFamily
    (Nat.le_trans (le_maximum (FL.fvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

/-- Family ladder reflection is progressive. -/
theorem flFamilyTransformer_progressive : Progressive flFamilyTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectFLFamily seed hi

/-- Every diagonal rank strictly exceeds the raw ladder transformer. -/
theorem flTransformer_lt_diagonal (schedule : BigNumber.WTree Nat) (k : Nat)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    flFamilyTransformer seed i n < diagonalLift schedule k flFamilyTransformer seed o n :=
  (diagonalLift_strictlyInflationary schedule k)
    flFamilyTransformer flFamilyTransformer_progressive seed i o n hi

/-- At every input, `F15` exceeds Contender 14's family. -/
theorem family14_lt_F15 (n : Nat) : family14 n < F15 n :=
  ((diagonalLift_preservesProgressive (schedule15 n) (rank15 n))
    flFamilyTransformer flFamilyTransformer_progressive)
    (fun _ => family14) 0 n n (Nat.zero_le n)

/-- The raw ladder reflection of Contender 14's family is below `F15`. -/
theorem raw_reflection_lt_F15 (n : Nat) : reflectFLFamily (fun _ => family14) n < F15 n :=
  flTransformer_lt_diagonal (schedule15 n) (rank15 n) (fun _ => family14) n n n (Nat.le_refl n)

/-- Every level-`n` ladder program of depth `≤ n`, run with the packed seed,
is below `F15 n`. -/
theorem fvalue_lt_F15 {n : Nat} {t : FL.CTm (FL.Atom n)} (ht : t ∈ FL.ladderUpTo n) :
    FL.fvalue n (packFamily (fun _ => family14)) n t < F15 n :=
  Nat.lt_trans (fvalue_lt_reflectFLFamily (fun _ => family14) ht) (raw_reflection_lt_F15 n)

theorem input_lt_family14 (n : Nat) : n < family14 n :=
  Nat.lt_trans (FL.input_lt_reflectFL family13 n) (FL.input_lt_reflectFL family13 (F14 n))

theorem input_lt_F15 (n : Nat) : n < F15 n :=
  Nat.lt_trans (input_lt_family14 n) (family14_lt_F15 n)

/-- **The required comparison**: Contender 14 is strictly smaller than Contender 15. -/
theorem contender_14_lt_contender_15 : contender_14 < contender_15 :=
  Nat.lt_trans (family14_lt_F15 42) (input_lt_F15 (F15 42))

theorem contender_13_lt_contender_15 : contender_13 < contender_15 :=
  Nat.lt_trans contender_13_lt_contender_14 contender_14_lt_contender_15

end BusyLean
