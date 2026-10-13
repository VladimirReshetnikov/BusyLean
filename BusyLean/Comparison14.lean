import BusyLean.Contender14
import BusyLean.HyperReflectionFacts
import BusyLean.Comparison13

/-! # Contender 14: comparison and domination theorems -/

namespace BusyLean

open BusyLean.W

/-! ## Dynamic-kind family reflection -/

theorem lt_reflectFdFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fd.fvalue (packFamily fs) n) (Fd.ctmsUpTo n))) :
    m < reflectFdFamily fs n := by
  unfold reflectFdFamily
  omega

theorem oracle_lt_reflectFdFamily (fs : Family) {i n : Nat}
    (hi : i ≤ n) : fs i n < reflectFdFamily fs n :=
  lt_reflectFdFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

theorem fvalue_lt_reflectFdFamily (fs : Family) {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily fs) n t < reflectFdFamily fs n :=
  lt_reflectFdFamily
    (Nat.le_trans (le_maximum (Fd.fvalue (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

theorem input_lt_reflectFdFamily (fs : Family) (n : Nat) :
    n < reflectFdFamily fs n := by
  unfold reflectFdFamily
  omega

/-- Dynamic-kind family reflection is progressive. -/
theorem fdFamilyTransformer_progressive :
    Progressive fdFamilyTransformer := by
  intro seed i o n hi
  exact oracle_lt_reflectFdFamily seed hi

/-! ## Hyperreflection margin -/

/-- Every diagonal rank strictly exceeds the raw dynamic-kind transformer. -/
theorem fdTransformer_lt_diagonal (schedule : BigNumber.WTree Nat) (k : Nat)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    fdFamilyTransformer seed i n <
      diagonalLift schedule k fdFamilyTransformer seed o n :=
  (diagonalLift_strictlyInflationary schedule k)
    fdFamilyTransformer fdFamilyTransformer_progressive seed i o n hi

/-- Consecutive diagonal ranks are strictly increasing for the actual base
transformer. -/
theorem fdDiagonal_rank_lt_succ (schedule : BigNumber.WTree Nat) (k : Nat)
    (seed : Family) (i o n : Nat) (hi : i ≤ n) :
    diagonalLift schedule k fdFamilyTransformer seed i n <
      diagonalLift schedule (k + 1) fdFamilyTransformer seed o n :=
  diagonalLift_rank_lt_succ schedule k fdFamilyTransformer
    fdFamilyTransformer_progressive seed i o n hi

/-- At every input, `F14` exceeds Contender 13's entire family. -/
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n := by
  exact ((diagonalLift_preservesProgressive (schedule14 n) (rank14 n))
    fdFamilyTransformer fdFamilyTransformer_progressive)
    (fun _ => family13) 0 n n (Nat.zero_le n)

/-- At every input, the raw dynamic-kind reflection layer is already below the
final hyperreflection layer. -/
theorem raw_reflection_lt_F14 (n : Nat) :
    reflectFdFamily (fun _ => family13) n < F14 n := by
  exact fdTransformer_lt_diagonal (schedule14 n) (rank14 n)
    (fun _ => family13) n n n (Nat.le_refl n)

/-- Every dynamic-kind program in the current syntax budget is below `F14`. -/
theorem fvalue_lt_F14 {n : Nat} {t : Fd.CTm} (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily (fun _ => family13)) n t < F14 n :=
  Nat.lt_trans (fvalue_lt_reflectFdFamily (fun _ => family13) ht)
    (raw_reflection_lt_F14 n)

/-- Contender 13's family itself grows past the input. -/
theorem input_lt_family13 (n : Nat) : n < family13 n :=
  Nat.lt_trans (Fd.input_lt_reflectFd family12 n)
    (Fd.input_lt_reflectFd family12 (F13 n))

/-- `F14` grows past its input. -/
theorem input_lt_F14 (n : Nat) : n < F14 n :=
  Nat.lt_trans (input_lt_family13 n) (family13_lt_F14 n)

/-- **The required comparison**: Contender 13 is strictly smaller than
Contender 14. -/
theorem contender_13_lt_contender_14 : contender_13 < contender_14 :=
  Nat.lt_trans (family13_lt_F14 42) (input_lt_F14 (F14 42))

/-- Hence every earlier accepted contender is also smaller. -/
theorem contender_12_lt_contender_14 : contender_12 < contender_14 :=
  Nat.lt_trans contender_12_lt_contender_13 contender_13_lt_contender_14

end BusyLean
