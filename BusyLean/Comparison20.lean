import BusyLean.Contender20
import BusyLean.Comparison19

/-! # Contender 20: exact comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- The additive guard in `reflectAFamily` strictly exceeds the finite maximum
it reflects. -/
theorem lt_reflectAFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.avalue (packFamily fs) n)
        (FL.autonomousLadderUpTo n))) :
    m < reflectAFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible oracle coordinate lies below one autonomous-universe
reflection step. -/
theorem oracle_lt_reflectAFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectAFamily fs n :=
  lt_reflectAFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every enumerated ramified-universe program lies below one reflection step. -/
theorem avalue_lt_reflectAFamily (fs : Family) {n : Nat}
    {t : FL.CTm Ordinal.WLevel} (ht : t ∈ FL.autonomousLadderUpTo n) :
    FL.avalue (packFamily fs) n t < reflectAFamily fs n :=
  lt_reflectAFamily
    (Nat.le_trans (le_maximum (FL.avalue (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- Autonomous-universe reflection is progressive. -/
theorem aTransformer_progressive : Progressive aTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectAFamily seed hi

/-- One more finite `F19` iterate is strictly larger.  No monotonicity of
`F19` is used. -/
theorem iterateF19_lt_succ (k n : Nat) :
    iterateF19 k n < iterateF19 (k + 1) n := by
  simpa only [iterateF19] using input_lt_F19 (iterateF19 k n)

/-- Coordinate zero of the seed orbit is exactly Contender 19's family. -/
theorem orbit19_zero (n : Nat) : orbit19 0 n = family19 n := rfl

/-- The exposed orbit is strictly increasing coordinate by coordinate. -/
theorem orbit19_lt_next (i n : Nat) : orbit19 i n < orbit19 (i + 1) n := by
  simpa only [orbit19, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using iterateF19_lt_succ (i + 2) n

/-- Every seed-orbit coordinate visible at input `n` lies below `F20 n`.
This is a substantially stronger lower bound than merely embedding coordinate
zero. -/
theorem orbit19_lt_F20 {i n : Nat} (hi : i ≤ n) : orbit19 i n < F20 n := by
  have h :=
    ((diagonalLift_preservesProgressive (schedule20 n) (rank20 n))
      aTransformer aTransformer_progressive)
      orbit19 i n n hi
  simpa only [F20] using h

/-- At every input, `F20` strictly exceeds Contender 19's family. -/
theorem family19_lt_F20 (n : Nat) : family19 n < F20 n := by
  have h :=
    ((diagonalLift_preservesProgressive (schedule20 n) (rank20 n))
      aTransformer aTransformer_progressive)
      orbit19 0 n n (Nat.zero_le n)
  simpa only [orbit19_zero, F20] using h

/-- The raw autonomous-universe reflection step is strictly below the full
ranked hyperreflection. -/
theorem raw_reflection_lt_F20 (n : Nat) :
    reflectAFamily orbit19 n < F20 n :=
  (diagonalLift_strictlyInflationary (schedule20 n) (rank20 n))
    aTransformer aTransformer_progressive orbit19 n n n (Nat.le_refl n)

/-- Every ramified-universe program of depth at most `n`, run with the packed
seed orbit, is below `F20 n`. -/
theorem avalue_lt_F20 {n : Nat} {t : FL.CTm Ordinal.WLevel}
    (ht : t ∈ FL.autonomousLadderUpTo n) :
    FL.avalue (packFamily orbit19) n t < F20 n :=
  Nat.lt_trans (avalue_lt_reflectAFamily orbit19 ht)
    (raw_reflection_lt_F20 n)

/-- The input lies below Contender 19's family. -/
theorem input_lt_family19 (n : Nat) : n < family19 n :=
  Nat.lt_trans (input_lt_F19 n) (input_lt_F19 (F19 n))

/-- `F20` is strictly inflationary on numerical inputs. -/
theorem input_lt_F20 (n : Nat) : n < F20 n :=
  Nat.lt_trans (input_lt_family19 n) (family19_lt_F20 n)

/-- Pointwise, the old function `F19` is already below the new function. -/
theorem F19_lt_F20 (n : Nat) : F19 n < F20 n :=
  Nat.lt_trans (input_lt_F19 (F19 n)) (family19_lt_F20 n)

/-- The inner stage already dominates 44 finite iterates of `F19` from 42. -/
theorem iterateF19_44_42_lt_F20_42 : iterateF19 44 42 < F20 42 := by
  simpa only [orbit19] using
    (orbit19_lt_F20 (i := 42) (n := 42) (Nat.le_refl 42))

/-- A strong closed lower bound for the final contender: it exceeds an
`F19`-orbit whose length is itself `F20 42 + 2`. -/
theorem long_F19_orbit_lt_contender_20 :
    iterateF19 (F20 42 + 2) (F20 42) < contender_20 := by
  simpa only [orbit19, contender_20] using
    (orbit19_lt_F20 (i := F20 42) (n := F20 42) (Nat.le_refl _))

/-- **The required exact comparison:** Contender 19 is strictly smaller than
Contender 20. -/
theorem contender_19_lt_contender_20 : contender_19 < contender_20 :=
  Nat.lt_trans (family19_lt_F20 42) (input_lt_F20 (F20 42))

/-- The new contender also strictly exceeds every earlier accepted contender
by transitivity. -/
theorem contender_18_lt_contender_20 : contender_18 < contender_20 :=
  Nat.lt_trans contender_18_lt_contender_19 contender_19_lt_contender_20

end BusyLean
