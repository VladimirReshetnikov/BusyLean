import BusyLean.Contender20
import BusyLean.Comparison19

/-! # Contender 20: comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- The finite-rank seed lift satisfies both iteration invariants. -/
theorem seedLift20_good (n : Nat) : GoodLift (seedLift20 n) :=
  ⟨diagonalLift_preservesProgressive (schedule20 n) (family19 n + 1),
    diagonalLift_strictlyInflationary (schedule20 n) (family19 n + 1)⟩

/-- The full W-rank lift satisfies both iteration invariants. -/
theorem lift20_good (n : Nat) : GoodLift (lift20 n) := by
  simpa [lift20] using
    treeDiagonalLift_good (schedule20 n) (rankTree20 n)
      (seedLift20 n) (seedLift20_good n)

/-- The raw large-Veblen reflection exceeds the Contender-19 seed family. -/
theorem family19_lt_raw20 (n : Nat) :
    family19 n < lTransformer seedFamily20 0 n := by
  change seedFamily20 0 n < lTransformer seedFamily20 0 n
  exact lTransformer_progressive seedFamily20 0 0 n (Nat.zero_le n)

/-- The finite diagonal rank strictly exceeds raw reflection. -/
theorem raw20_lt_seedLift20 (n : Nat) :
    lTransformer seedFamily20 0 n <
      seedLift20 n lTransformer seedFamily20 0 n := by
  simpa [seedLift20] using
    (diagonalLift_strictlyInflationary
      (schedule20 n) (family19 n + 1))
      lTransformer lTransformer_progressive
      seedFamily20 0 0 n (Nat.zero_le n)

/-- The outer W-rank stage strictly exceeds its already enormous seed lift. -/
theorem seedLift20_lt_F20 (n : Nat) :
    seedLift20 n lTransformer seedFamily20 0 n < F20 n := by
  change seedLift20 n lTransformer seedFamily20 0 n <
    lift20 n lTransformer seedFamily20 n n
  simpa [lift20] using
    seed_lt_treeDiagonalLift (schedule20 n) (rankTree20 n)
      (seedLift20 n) (seedLift20_good n)
      lTransformer lTransformer_progressive
      seedFamily20 0 n n (Nat.zero_le n)

/-- Raw reflection is below the complete Contender-20 stage. -/
theorem raw_reflection20_lt_F20 (n : Nat) :
    reflectLFamily seedFamily20 n < F20 n := by
  change lTransformer seedFamily20 0 n < F20 n
  exact Nat.lt_trans (raw20_lt_seedLift20 n) (seedLift20_lt_F20 n)

/-- Pointwise domination of Contender 19's family. -/
theorem family19_lt_F20 (n : Nat) : family19 n < F20 n :=
  Nat.lt_trans (family19_lt_raw20 n) (raw_reflection20_lt_F20 n)

/-- Every large-Veblen-ladder program in the bounded enumeration lies below
`F20 n`. -/
theorem lvalue_lt_F20 {n : Nat} {t : FL.CTm Ordinal.LargeVeblen}
    (ht : t ∈ FL.lveblenLadderUpTo n) :
    FL.lvalue (packFamily seedFamily20) n t < F20 n :=
  Nat.lt_trans (lvalue_lt_reflectLFamily seedFamily20 ht)
    (raw_reflection20_lt_F20 n)

/-- The input is below Contender 19's self-composed family. -/
theorem input_lt_family19 (n : Nat) : n < family19 n :=
  Nat.lt_trans (input_lt_F19 n) (input_lt_F19 (F19 n))

/-- Every input is below the corresponding Contender-20 family value. -/
theorem input_lt_F20 (n : Nat) : n < F20 n :=
  Nat.lt_trans (input_lt_family19 n) (family19_lt_F20 n)

/-- The required formal comparison. -/
theorem contender_19_lt_contender_20 : contender_19 < contender_20 :=
  Nat.lt_trans (family19_lt_F20 42) (input_lt_F20 (F20 42))

/-- A convenient inherited comparison. -/
theorem contender_18_lt_contender_20 : contender_18 < contender_20 :=
  Nat.lt_trans contender_18_lt_contender_19 contender_19_lt_contender_20

end BusyLean
