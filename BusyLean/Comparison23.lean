import BusyLean.Contender23
import BusyLean.TreeHyperReflectionFacts
import BusyLean.Comparison22

/-! # Contender 23: comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- At every input, `F23` exceeds Contender 22's family. -/
theorem family22_lt_F23 (n : Nat) : family22 n < F23 n :=
  ((wDiagonalLift_preservesProgressive (schedule23 n) (rank23 n))
    twTransformer twTransformer_progressive)
    (fun _ => family22) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F23 (n : Nat) : reflectTwFamily (fun _ => family22) n < F23 n :=
  (wDiagonalLift_strictlyInflationary (schedule23 n) (rank23 n))
    twTransformer twTransformer_progressive (fun _ => family22) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the atoms of `tower n`, run with the packed
seed, is below `F23 n`. -/
theorem tvalue22_lt_F23 {n : Nat} {t : FL.CTm ((Ordinal.tower n).T)} (ht : t ∈ FL.towerLadderUpTo n) :
    FL.tvalue22 n (packFamily (fun _ => family22)) n t < F23 n :=
  Nat.lt_trans (tvalue22_lt_reflectTwFamily (fun _ => family22) ht) (raw_reflection_lt_F23 n)

theorem input_lt_family22 (n : Nat) : n < family22 n :=
  Nat.lt_trans (input_lt_F22 n) (input_lt_F22 (F22 n))

theorem input_lt_F23 (n : Nat) : n < F23 n :=
  Nat.lt_trans (input_lt_family22 n) (family22_lt_F23 n)

/-- **The required comparison**: Contender 22 is strictly smaller than Contender 23. -/
theorem contender_22_lt_contender_23 : contender_22 < contender_23 :=
  Nat.lt_trans (family22_lt_F23 42) (input_lt_F23 (F23 42))

theorem contender_21_lt_contender_23 : contender_21 < contender_23 :=
  Nat.lt_trans contender_21_lt_contender_22 contender_22_lt_contender_23

end BusyLean
