import BusyLean.Contender31
import BusyLean.Comparison30

/-! # Contender 31: comparison and domination theorems -/

namespace BusyLean

open BusyLean.W

/-- The old raw finite-type reflection is strictly below the new budget. -/
theorem reflectTLFamily_lt_budget31 (fs : Family) (n : Nat) :
    reflectTLFamily fs n < budget31 fs n := by
  unfold budget31
  omega

/-- Every visible oracle coordinate is strictly below the reflection-generated
budget. -/
theorem oracle_lt_budget31 (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < budget31 fs n :=
  Nat.lt_trans (oracle_lt_reflectTLFamily fs hi)
    (reflectTLFamily_lt_budget31 fs n)

/-- The external input is strictly below the reflection-generated budget. -/
theorem input_lt_budget31 (fs : Family) (n : Nat) :
    n < budget31 fs n := by
  unfold budget31
  omega

/-- The selected type-level/depth/fuel budget is strictly below the new raw
reflection. -/
theorem budget31_lt_reflectTLStarFamily (fs : Family) (n : Nat) :
    budget31 fs n < reflectTLStarFamily fs n := by
  unfold reflectTLStarFamily
  omega

/-- General maximum-to-reflection comparison. -/
theorem lt_reflectTLStarFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.tlvalue (budget31 fs n) (packFamily fs) (budget31 fs n))
        (FL.tltreeLadderUpTo (budget31 fs n)))) :
    m < reflectTLStarFamily fs n := by
  unfold reflectTLStarFamily
  omega

/-- Every visible oracle coordinate is strictly below the new raw reflector. -/
theorem oracle_lt_reflectTLStarFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectTLStarFamily fs n :=
  lt_reflectTLStarFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every accepted program at the reflection-generated type-level/depth/fuel
budget is below the raw reflector. -/
theorem tlStarValue_lt_reflectTLStarFamily (fs : Family) {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.typeLevelTree (budget31 fs n)))}
    (ht : t ∈ FL.tltreeLadderUpTo (budget31 fs n)) :
    FL.tlvalue (budget31 fs n) (packFamily fs) (budget31 fs n) t <
      reflectTLStarFamily fs n :=
  lt_reflectTLStarFamily
    (Nat.le_trans
      (le_maximum
        (FL.tlvalue (budget31 fs n) (packFamily fs) (budget31 fs n)) ht)
      (BigNumber.le_maxN_right _ _))

/-- Reflection-indexed finite-type reflection is progressive. -/
theorem tlStarTransformer_progressive : Progressive tlStarTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectTLStarFamily seed hi

/-- At every input, `F31` exceeds Contender 30's entire family. -/
theorem family30_lt_F31 (n : Nat) : family30 n < F31 n :=
  ((wDiagonalLift_preservesProgressive (schedule31 n) (rank31 n))
    tlStarTransformer tlStarTransformer_progressive)
    (fun _ => family30) 0 n n (Nat.zero_le n)

/-- The raw reflection-indexed finite-type reflector is strictly below the
W-ranked construction. -/
theorem raw_reflection_lt_F31 (n : Nat) :
    reflectTLStarFamily (fun _ => family30) n < F31 n :=
  (wDiagonalLift_strictlyInflationary (schedule31 n) (rank31 n))
    tlStarTransformer tlStarTransformer_progressive
    (fun _ => family30) n n n (Nat.le_refl n)

/-- The self-selected finite type/depth/fuel budget is strictly below `F31`. -/
theorem height31_lt_F31 (n : Nat) : height31 n < F31 n :=
  Nat.lt_trans
    (budget31_lt_reflectTLStarFamily (fun _ => family30) n)
    (raw_reflection_lt_F31 n)

/-- Every accepted program over
`Addr (typeLevelTree (height31 n))`, at depth and fuel `height31 n`, is below
`F31 n`. -/
theorem tlStarValue_lt_F31 {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.typeLevelTree (height31 n)))}
    (ht : t ∈ FL.tltreeLadderUpTo (height31 n)) :
    FL.tlvalue (height31 n) (packFamily (fun _ => family30)) (height31 n) t <
      F31 n :=
  Nat.lt_trans
    (tlStarValue_lt_reflectTLStarFamily (fun _ => family30) ht)
    (raw_reflection_lt_F31 n)

/-- At the contest input, the incumbent raw reflector, run with Contender 30's
family as oracle, is already below the new finite type level. -/
theorem old_raw30_lt_height31_42 :
    reflectTLFamily (fun _ => family30) 42 < height31 42 :=
  reflectTLFamily_lt_budget31 (fun _ => family30) 42

/-- At the contest input, the selected finite type level strictly exceeds
Contender 30. -/
theorem contender_30_lt_height31_42 : contender_30 < height31 42 :=
  oracle_lt_budget31 (fun _ => family30)
    (i := 0) (n := 42) (Nat.zero_le 42)

/-- Contender 30 is below the new raw reflection even before W-ranked
hyperreflection is applied. -/
theorem contender_30_lt_raw31_42 :
    contender_30 < reflectTLStarFamily (fun _ => family30) 42 :=
  Nat.lt_trans contender_30_lt_height31_42
    (budget31_lt_reflectTLStarFamily (fun _ => family30) 42)

theorem input_lt_family30 (n : Nat) : n < family30 n :=
  Nat.lt_trans (input_lt_F30 n) (input_lt_F30 (F30 n))

theorem input_lt_F31 (n : Nat) : n < F31 n :=
  Nat.lt_trans (input_lt_family30 n) (family30_lt_F31 n)

/-- The complete formal margin at the contest input:

`Contender 30 < selected type level < raw new reflection < F31 42 < Contender 31`.
-/
theorem contender_30_lt_selected_F31 : contender_30 < F31 42 :=
  Nat.lt_trans contender_30_lt_raw31_42 (raw_reflection_lt_F31 42)

/-- **The required comparison:** Contender 30 is strictly smaller than
Contender 31. -/
theorem contender_30_lt_contender_31 : contender_30 < contender_31 :=
  Nat.lt_trans (family30_lt_F31 42) (input_lt_F31 (F31 42))

/-- Convenient transitive comparisons with previous accepted entries. -/
theorem contender_29_lt_contender_31 : contender_29 < contender_31 :=
  Nat.lt_trans contender_29_lt_contender_30 contender_30_lt_contender_31

theorem contender_28_lt_contender_31 : contender_28 < contender_31 :=
  Nat.lt_trans contender_28_lt_contender_30 contender_30_lt_contender_31

end BusyLean
