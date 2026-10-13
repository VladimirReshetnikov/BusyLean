import BusyLean.Contender20
import BusyLean.Comparison19

/-! # Contender 20: comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- At every input, `F20` exceeds Contender 19's entire family. -/
theorem family19_lt_F20 (n : Nat) : family19 n < F20 n :=
  ((wDiagonalLift_preservesProgressive (schedule20 n) (rank20 n))
    lTransformer lTransformer_progressive)
    (fun _ => family19) 0 n n (Nat.zero_le n)

/-- The single raw large-Veblen reflection step over the new seed is already
strictly below the W-ranked construction. -/
theorem raw_reflection_lt_F20 (n : Nat) :
    reflectLFamily (fun _ => family19) n < F20 n :=
  (wDiagonalLift_strictlyInflationary (schedule20 n) (rank20 n))
    lTransformer lTransformer_progressive
    (fun _ => family19) n n n (Nat.le_refl n)

/-- Every large-Veblen-ladder program of depth `≤ n`, run with the packed
Contender 19 family, is below `F20 n`. -/
theorem lvalue_lt_F20 {n : Nat} {t : FL.CTm Ordinal.LargeVeblen}
    (ht : t ∈ FL.lveblenLadderUpTo n) :
    FL.lvalue (packFamily (fun _ => family19)) n t < F20 n :=
  Nat.lt_trans (lvalue_lt_reflectLFamily (fun _ => family19) ht)
    (raw_reflection_lt_F20 n)

/-- Even the un-doubled function `F19` is pointwise below `F20`. -/
theorem F19_lt_F20 (n : Nat) : F19 n < F20 n :=
  Nat.lt_trans (input_lt_F19 (F19 n)) (family19_lt_F20 n)

theorem input_lt_family19 (n : Nat) : n < family19 n :=
  Nat.lt_trans (input_lt_F19 n) (input_lt_F19 (F19 n))

theorem input_lt_F20 (n : Nat) : n < F20 n :=
  Nat.lt_trans (input_lt_family19 n) (family19_lt_F20 n)

/-- **The required comparison:** Contender 19 is strictly smaller than
Contender 20. -/
theorem contender_19_lt_contender_20 : contender_19 < contender_20 :=
  Nat.lt_trans (family19_lt_F20 42) (input_lt_F20 (F20 42))

/-- A convenient transitive comparison with the previous two contenders. -/
theorem contender_18_lt_contender_20 : contender_18 < contender_20 :=
  Nat.lt_trans contender_18_lt_contender_19 contender_19_lt_contender_20

end BusyLean
