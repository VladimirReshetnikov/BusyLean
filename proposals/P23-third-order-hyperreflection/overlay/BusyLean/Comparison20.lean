import BusyLean.Contender20
import BusyLean.SuperReflectionFacts
import BusyLean.Comparison19

/-! # Contender 20: comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- The current-style lift used as the base of Contender 20 satisfies both
higher invariants. -/
theorem diagonalLift20_good (n : Nat) :
    GoodLift (diagonalLift (schedule20 n) (innerRank20 n)) :=
  ⟨diagonalLift_preservesProgressive
      (schedule20 n) (innerRank20 n),
    diagonalLift_strictlyInflationary
      (schedule20 n) (innerRank20 n)⟩

/-- The final third-order lift is good. -/
theorem lift20_good (n : Nat) : GoodLift (lift20 n) := by
  simpa [lift20] using
    (superIterate_good (schedule20 n)
      (diagonalLift (schedule20 n) (innerRank20 n))
      (diagonalLift20_good n) (metaRank20 n))

/-- `lift20 n` preserves progressive transformers. -/
theorem lift20_preservesProgressive (n : Nat) :
    PreservesProgressive (lift20 n) :=
  (lift20_good n).1

/-- `lift20 n` strictly exceeds every progressive base transformer. -/
theorem lift20_strictlyInflationary (n : Nat) :
    StrictlyInflationary (lift20 n) :=
  (lift20_good n).2

/-- Formal architectural gain: the complete third-order lift strictly exceeds
its own initial current-style diagonal hyperlift, at every visible coordinate.
-/
theorem diagonalLift_lt_lift20 (n : Nat)
    (base : Transformer) (hbase : Progressive base)
    (seed : Family) (i o : Nat) (hi : i ≤ n) :
    diagonalLift (schedule20 n) (innerRank20 n)
        base seed i n <
      lift20 n base seed o n := by
  simpa [lift20, metaRank20] using
    (lift_lt_superIterate_succ (schedule20 n)
      (diagonalLift (schedule20 n) (innerRank20 n))
      (diagonalLift20_good n) (family19 n)
      base hbase seed i o n hi)

/-- The preceding family is already beaten inside the produced hyper-family. -/
theorem family19_lt_hyperFamily20 (n : Nat) :
    family19 n < hyperFamily20 n 0 n := by
  have h := (lift20_preservesProgressive n)
    lTransformer lTransformer_progressive seed19 0 0 n (Nat.zero_le n)
  simpa [seed19, hyperFamily20] using h

/-- Every visible coordinate of the produced family is below the final
large-Veblen reflection. -/
theorem hyperFamily20_lt_F20 {i n : Nat} (hi : i ≤ n) :
    hyperFamily20 n i n < F20 n := by
  simpa [F20] using
    (oracle_lt_reflectLFamily (hyperFamily20 n) (i := i) (n := n) hi)

/-- At every input, `F20` exceeds Contender 19's complete family. -/
theorem family19_lt_F20 (n : Nat) : family19 n < F20 n :=
  Nat.lt_trans (family19_lt_hyperFamily20 n)
    (hyperFamily20_lt_F20 (n := n) (i := 0) (Nat.zero_le n))

/-- Even the raw large-Veblen reflection over the old seed is below the
third-order family. -/
theorem raw_reflection_lt_hyperFamily20 (n : Nat) :
    reflectLFamily seed19 n < hyperFamily20 n 0 n := by
  have h := (lift20_strictlyInflationary n)
    lTransformer lTransformer_progressive seed19 n 0 n (Nat.le_refl n)
  simpa [lTransformer, hyperFamily20] using h

/-- The raw large-Veblen reflection over the old seed is below `F20`. -/
theorem raw_reflection_lt_F20 (n : Nat) :
    reflectLFamily seed19 n < F20 n :=
  Nat.lt_trans (raw_reflection_lt_hyperFamily20 n)
    (hyperFamily20_lt_F20 (n := n) (i := 0) (Nat.zero_le n))

/-- Every enumerated large-Veblen-ladder program run against the final packed
third-order family is below `F20 n`. -/
theorem final_lvalue_lt_F20 {n : Nat}
    {t : FL.CTm Ordinal.LargeVeblen}
    (ht : t ∈ FL.lveblenLadderUpTo n) :
    FL.lvalue (packFamily (hyperFamily20 n)) n t < F20 n := by
  simpa [F20] using
    (lvalue_lt_reflectLFamily (hyperFamily20 n) ht)

/-- The numerical input is below the preceding family. -/
theorem input_lt_family19 (n : Nat) : n < family19 n := by
  simpa [family19] using
    (Nat.lt_trans (input_lt_F19 n) (input_lt_F19 (F19 n)))

/-- The numerical input is below `F20`. -/
theorem input_lt_F20 (n : Nat) : n < F20 n :=
  Nat.lt_trans (input_lt_family19 n) (family19_lt_F20 n)

/-- The required comparison: Contender 19 is strictly below Contender 20. -/
theorem contender_19_lt_contender_20 : contender_19 < contender_20 := by
  simpa [family19, contender_19, contender_20] using
    (Nat.lt_trans (family19_lt_F20 42)
      (input_lt_F20 (F20 42)))

/-- A convenient transitive comparison with Contender 18. -/
theorem contender_18_lt_contender_20 : contender_18 < contender_20 :=
  Nat.lt_trans contender_18_lt_contender_19 contender_19_lt_contender_20

end BusyLean
