import BusyLean.Contender28
import BusyLean.Comparison27

/-! # Contender 28: comparison and domination theorems -/

namespace BusyLean

open BusyLean.W

/-- The old raw universe reflection is strictly below the new budget. -/
theorem reflectUFamily_lt_budget28 (fs : Family) (n : Nat) :
    reflectUFamily fs n < budget28 fs n := by
  unfold budget28
  omega

/-- Every visible oracle coordinate is strictly below the reflection-generated
budget. -/
theorem oracle_lt_budget28 (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < budget28 fs n :=
  Nat.lt_trans (oracle_lt_reflectUFamily fs hi)
    (reflectUFamily_lt_budget28 fs n)

/-- The external input is strictly below the reflection-generated budget. -/
theorem input_lt_budget28 (fs : Family) (n : Nat) :
    n < budget28 fs n := by
  unfold budget28
  omega

/-- The selected universe/depth/fuel budget is strictly below the new raw
reflection. -/
theorem budget28_lt_reflectUStarFamily (fs : Family) (n : Nat) :
    budget28 fs n < reflectUStarFamily fs n := by
  unfold reflectUStarFamily
  omega

/-- General maximum-to-reflection comparison. -/
theorem lt_reflectUStarFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.uvalue (budget28 fs n) (packFamily fs) (budget28 fs n))
        (FL.utreeLadderUpTo (budget28 fs n)))) :
    m < reflectUStarFamily fs n := by
  unfold reflectUStarFamily
  omega

/-- Every visible oracle coordinate is strictly below the new raw reflector. -/
theorem oracle_lt_reflectUStarFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectUStarFamily fs n :=
  lt_reflectUStarFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every accepted program at the reflection-generated universe/depth/fuel
budget is below the raw reflector. -/
theorem uStarValue_lt_reflectUStarFamily (fs : Family) {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.universeLadderTree (budget28 fs n)))}
    (ht : t ∈ FL.utreeLadderUpTo (budget28 fs n)) :
    FL.uvalue (budget28 fs n) (packFamily fs) (budget28 fs n) t <
      reflectUStarFamily fs n :=
  lt_reflectUStarFamily
    (Nat.le_trans
      (le_maximum
        (FL.uvalue (budget28 fs n) (packFamily fs) (budget28 fs n)) ht)
      (BigNumber.le_maxN_right _ _))

/-- Reflection-indexed universe-address reflection is progressive. -/
theorem uStarTransformer_progressive : Progressive uStarTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectUStarFamily seed hi

/-- At every input, `F28` exceeds Contender 27's entire family. -/
theorem family27_lt_F28 (n : Nat) : family27 n < F28 n :=
  ((wDiagonalLift_preservesProgressive (schedule28 n) (rank28 n))
    uStarTransformer uStarTransformer_progressive)
    (fun _ => family27) 0 n n (Nat.zero_le n)

/-- The raw reflection-indexed universe reflector is strictly below the
W-ranked construction. -/
theorem raw_reflection_lt_F28 (n : Nat) :
    reflectUStarFamily (fun _ => family27) n < F28 n :=
  (wDiagonalLift_strictlyInflationary (schedule28 n) (rank28 n))
    uStarTransformer uStarTransformer_progressive
    (fun _ => family27) n n n (Nat.le_refl n)

/-- The self-selected finite universe/depth/fuel budget is strictly below
`F28`. -/
theorem height28_lt_F28 (n : Nat) : height28 n < F28 n :=
  Nat.lt_trans
    (budget28_lt_reflectUStarFamily (fun _ => family27) n)
    (raw_reflection_lt_F28 n)

/-- Every accepted program over
`Addr (universeLadderTree (height28 n))`, at depth and fuel `height28 n`, is
below `F28 n`. -/
theorem uStarValue_lt_F28 {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.universeLadderTree (height28 n)))}
    (ht : t ∈ FL.utreeLadderUpTo (height28 n)) :
    FL.uvalue (height28 n) (packFamily (fun _ => family27)) (height28 n) t <
      F28 n :=
  Nat.lt_trans
    (uStarValue_lt_reflectUStarFamily (fun _ => family27) ht)
    (raw_reflection_lt_F28 n)

/-- At the contest input, the incumbent raw reflector, run with Contender 27's
family as oracle, is already below the new universe index. -/
theorem old_raw27_lt_height28_42 :
    reflectUFamily (fun _ => family27) 42 < height28 42 :=
  reflectUFamily_lt_budget28 (fun _ => family27) 42

/-- At the contest input, the new universe index strictly exceeds Contender
27. -/
theorem contender_27_lt_height28_42 : contender_27 < height28 42 :=
  oracle_lt_budget28 (fun _ => family27)
    (i := 0) (n := 42) (Nat.zero_le 42)

/-- Contender 27 is below the new raw reflection even before W-ranked
hyperreflection is applied. -/
theorem contender_27_lt_raw28_42 :
    contender_27 < reflectUStarFamily (fun _ => family27) 42 :=
  Nat.lt_trans contender_27_lt_height28_42
    (budget28_lt_reflectUStarFamily (fun _ => family27) 42)

theorem input_lt_family27 (n : Nat) : n < family27 n :=
  Nat.lt_trans (input_lt_F27 n) (input_lt_F27 (F27 n))

theorem input_lt_F28 (n : Nat) : n < F28 n :=
  Nat.lt_trans (input_lt_family27 n) (family27_lt_F28 n)

/-- The complete formal margin at the contest input:

`Contender 27 < selected universe index < raw new reflection < F28 42 < Contender 28`.
-/
theorem contender_27_lt_selected_F28 : contender_27 < F28 42 :=
  Nat.lt_trans contender_27_lt_raw28_42 (raw_reflection_lt_F28 42)

/-- **The required comparison:** Contender 27 is strictly smaller than
Contender 28. -/
theorem contender_27_lt_contender_28 : contender_27 < contender_28 :=
  Nat.lt_trans (family27_lt_F28 42) (input_lt_F28 (F28 42))

/-- Convenient transitive comparisons with the previous accepted entries. -/
theorem contender_26_lt_contender_28 : contender_26 < contender_28 :=
  Nat.lt_trans contender_26_lt_contender_27 contender_27_lt_contender_28

theorem contender_25_lt_contender_28 : contender_25 < contender_28 :=
  Nat.lt_trans contender_25_lt_contender_27 contender_27_lt_contender_28

end BusyLean
