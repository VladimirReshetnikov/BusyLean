import BusyLean.Contender22
import BusyLean.Comparison21

/-! # Contender 22: comparison and domination theorems -/

namespace BusyLean

open BusyLean.W

/-- Every visible oracle coordinate is strictly below the self budget. -/
theorem oracle_lt_budget22 (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < budget22 fs n := by
  unfold budget22
  have h := le_prefixMax (fun j => fs j n) hi
  omega

/-- The external input is strictly below the self budget. -/
theorem input_lt_budget22 (fs : Family) (n : Nat) :
    n < budget22 fs n := by
  unfold budget22
  omega

/-- The self budget is itself strictly below the raw self-budgeted reflection. -/
theorem budget22_lt_reflectZStarFamily (fs : Family) (n : Nat) :
    budget22 fs n < reflectZStarFamily fs n := by
  unfold reflectZStarFamily
  omega

/-- General maximum-to-reflection comparison. -/
theorem lt_reflectZStarFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.zvalue (budget22 fs n) (packFamily fs) (budget22 fs n))
        (FL.buchholzLadderUpTo (budget22 fs n)))) :
    m < reflectZStarFamily fs n := by
  unfold reflectZStarFamily
  omega

/-- Every visible oracle coordinate is strictly below the raw reflector. -/
theorem oracle_lt_reflectZStarFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectZStarFamily fs n :=
  lt_reflectZStarFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every accepted program at the self-selected Buchholz budget is below the
raw reflector. -/
theorem zStarValue_lt_reflectZStarFamily (fs : Family) {n : Nat}
    {t : FL.CTm (Ordinal.Buchholz (budget22 fs n))}
    (ht : t ∈ FL.buchholzLadderUpTo (budget22 fs n)) :
    FL.zvalue (budget22 fs n) (packFamily fs) (budget22 fs n) t <
      reflectZStarFamily fs n :=
  lt_reflectZStarFamily
    (Nat.le_trans
      (le_maximum
        (FL.zvalue (budget22 fs n) (packFamily fs) (budget22 fs n)) ht)
      (BigNumber.le_maxN_right _ _))

/-- Self-budgeted Buchholz reflection is progressive. -/
theorem zStarTransformer_progressive : Progressive zStarTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectZStarFamily seed hi

/-- At every input, `F22` exceeds Contender 21's entire family. -/
theorem family21_lt_F22 (n : Nat) : family21 n < F22 n :=
  ((wDiagonalLift_preservesProgressive (schedule22 n) (rank22 n))
    zStarTransformer zStarTransformer_progressive)
    (fun _ => family21) 0 n n (Nat.zero_le n)

/-- The raw self-budgeted reflection over the Contender 21 seed is strictly
below the W-ranked construction. -/
theorem raw_reflection_lt_F22 (n : Nat) :
    reflectZStarFamily (fun _ => family21) n < F22 n :=
  (wDiagonalLift_strictlyInflationary (schedule22 n) (rank22 n))
    zStarTransformer zStarTransformer_progressive
    (fun _ => family21) n n n (Nat.le_refl n)

/-- The self-selected finite budget is strictly below `F22`. -/
theorem height22_lt_F22 (n : Nat) : height22 n < F22 n :=
  Nat.lt_trans
    (budget22_lt_reflectZStarFamily (fun _ => family21) n)
    (raw_reflection_lt_F22 n)

/-- Every accepted program at the self-selected level/depth/fuel budget is
below `F22 n`. -/
theorem zStarValue_lt_F22 {n : Nat}
    {t : FL.CTm (Ordinal.Buchholz (height22 n))}
    (ht : t ∈ FL.buchholzLadderUpTo (height22 n)) :
    FL.zvalue (height22 n) (packFamily (fun _ => family21)) (height22 n) t <
      F22 n :=
  Nat.lt_trans
    (zStarValue_lt_reflectZStarFamily (fun _ => family21) ht)
    (raw_reflection_lt_F22 n)

/-- At the contest input, the new finite syntax/level budget already exceeds
Contender 21. -/
theorem contender_21_lt_height22_42 : contender_21 < height22 42 := by
  exact oracle_lt_budget22 (fun _ => family21)
    (i := 0) (n := 42) (Nat.zero_le 42)

/-- Contender 21 is below the raw self-budgeted reflection even before W-ranked
hyperreflection is applied. -/
theorem contender_21_lt_raw22_42 :
    contender_21 < reflectZStarFamily (fun _ => family21) 42 :=
  Nat.lt_trans contender_21_lt_height22_42
    (budget22_lt_reflectZStarFamily (fun _ => family21) 42)

theorem input_lt_family21 (n : Nat) : n < family21 n :=
  Nat.lt_trans (input_lt_F21 n) (input_lt_F21 (F21 n))

theorem input_lt_F22 (n : Nat) : n < F22 n :=
  Nat.lt_trans (input_lt_family21 n) (family21_lt_F22 n)

/-- **The required comparison:** Contender 21 is strictly smaller than
Contender 22. -/
theorem contender_21_lt_contender_22 : contender_21 < contender_22 :=
  Nat.lt_trans (family21_lt_F22 42) (input_lt_F22 (F22 42))

/-- A convenient transitive comparison with Contender 20. -/
theorem contender_20_lt_contender_22 : contender_20 < contender_22 :=
  Nat.lt_trans contender_20_lt_contender_21 contender_21_lt_contender_22

end BusyLean
