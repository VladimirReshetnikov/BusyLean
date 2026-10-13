import BusyLean.Contender26
import BusyLean.Comparison25

/-! # Contender 26: comparison and domination theorems -/

namespace BusyLean

open BusyLean.W

/-- The old raw address reflection is strictly below the new budget. -/
theorem reflectAFamily_lt_budget26 (fs : Family) (n : Nat) :
    reflectAFamily fs n < budget26 fs n := by
  unfold budget26
  omega

/-- Every visible oracle coordinate is strictly below the reflection-generated
budget. -/
theorem oracle_lt_budget26 (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < budget26 fs n :=
  Nat.lt_trans (oracle_lt_reflectAFamily fs hi)
    (reflectAFamily_lt_budget26 fs n)

/-- The external input is strictly below the reflection-generated budget. -/
theorem input_lt_budget26 (fs : Family) (n : Nat) :
    n < budget26 fs n := by
  unfold budget26
  omega

/-- The selected tree/depth/fuel budget is strictly below the new raw
reflection. -/
theorem budget26_lt_reflectAStarFamily (fs : Family) (n : Nat) :
    budget26 fs n < reflectAStarFamily fs n := by
  unfold reflectAStarFamily
  omega

/-- General maximum-to-reflection comparison. -/
theorem lt_reflectAStarFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.avalue (budget26 fs n) (packFamily fs) (budget26 fs n))
        (FL.addrLadderUpTo (budget26 fs n)))) :
    m < reflectAStarFamily fs n := by
  unfold reflectAStarFamily
  omega

/-- Every visible oracle coordinate is strictly below the new raw reflector. -/
theorem oracle_lt_reflectAStarFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectAStarFamily fs n :=
  lt_reflectAStarFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every accepted program at the reflection-generated tree/depth/fuel budget
is below the raw reflector. -/
theorem aStarValue_lt_reflectAStarFamily (fs : Family) {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.bigTree (budget26 fs n)))}
    (ht : t ∈ FL.addrLadderUpTo (budget26 fs n)) :
    FL.avalue (budget26 fs n) (packFamily fs) (budget26 fs n) t <
      reflectAStarFamily fs n :=
  lt_reflectAStarFamily
    (Nat.le_trans
      (le_maximum
        (FL.avalue (budget26 fs n) (packFamily fs) (budget26 fs n)) ht)
      (BigNumber.le_maxN_right _ _))

/-- Reflection-indexed address-ladder reflection is progressive. -/
theorem aStarTransformer_progressive : Progressive aStarTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectAStarFamily seed hi

/-- At every input, `F26` exceeds Contender 25's entire family. -/
theorem family25_lt_F26 (n : Nat) : family25 n < F26 n :=
  ((wDiagonalLift_preservesProgressive (schedule26 n) (rank26 n))
    aStarTransformer aStarTransformer_progressive)
    (fun _ => family25) 0 n n (Nat.zero_le n)

/-- The raw reflection-indexed address reflector is strictly below the W-ranked
construction. -/
theorem raw_reflection_lt_F26 (n : Nat) :
    reflectAStarFamily (fun _ => family25) n < F26 n :=
  (wDiagonalLift_strictlyInflationary (schedule26 n) (rank26 n))
    aStarTransformer aStarTransformer_progressive
    (fun _ => family25) n n n (Nat.le_refl n)

/-- The self-selected finite tree/depth/fuel budget is strictly below `F26`. -/
theorem height26_lt_F26 (n : Nat) : height26 n < F26 n :=
  Nat.lt_trans
    (budget26_lt_reflectAStarFamily (fun _ => family25) n)
    (raw_reflection_lt_F26 n)

/-- Every accepted program over `Addr (bigTree (height26 n))`, at depth and
fuel `height26 n`, is below `F26 n`. -/
theorem aStarValue_lt_F26 {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.bigTree (height26 n)))}
    (ht : t ∈ FL.addrLadderUpTo (height26 n)) :
    FL.avalue (height26 n) (packFamily (fun _ => family25)) (height26 n) t <
      F26 n :=
  Nat.lt_trans
    (aStarValue_lt_reflectAStarFamily (fun _ => family25) ht)
    (raw_reflection_lt_F26 n)

/-- At the contest input, the incumbent raw reflector, run with Contender 25's
family as oracle, is already below the new tree index. -/
theorem old_raw25_lt_height26_42 :
    reflectAFamily (fun _ => family25) 42 < height26 42 :=
  reflectAFamily_lt_budget26 (fun _ => family25) 42

/-- At the contest input, the new tree index strictly exceeds Contender 25. -/
theorem contender_25_lt_height26_42 : contender_25 < height26 42 :=
  oracle_lt_budget26 (fun _ => family25)
    (i := 0) (n := 42) (Nat.zero_le 42)

/-- Contender 25 is below the new raw reflection even before W-ranked
hyperreflection is applied. -/
theorem contender_25_lt_raw26_42 :
    contender_25 < reflectAStarFamily (fun _ => family25) 42 :=
  Nat.lt_trans contender_25_lt_height26_42
    (budget26_lt_reflectAStarFamily (fun _ => family25) 42)

theorem input_lt_family25 (n : Nat) : n < family25 n :=
  Nat.lt_trans (input_lt_F25 n) (input_lt_F25 (F25 n))

theorem input_lt_F26 (n : Nat) : n < F26 n :=
  Nat.lt_trans (input_lt_family25 n) (family25_lt_F26 n)

/-- The complete formal margin at the contest input:

`Contender 25 < selected tree index < raw new reflection < F26 42 < Contender 26`.
-/
theorem contender_25_lt_selected_F26 : contender_25 < F26 42 :=
  Nat.lt_trans contender_25_lt_raw26_42 (raw_reflection_lt_F26 42)

/-- **The required comparison:** Contender 25 is strictly smaller than
Contender 26. -/
theorem contender_25_lt_contender_26 : contender_25 < contender_26 :=
  Nat.lt_trans (family25_lt_F26 42) (input_lt_F26 (F26 42))

/-- Convenient transitive comparisons with the previous two accepted entries. -/
theorem contender_24_lt_contender_26 : contender_24 < contender_26 :=
  Nat.lt_trans contender_24_lt_contender_25 contender_25_lt_contender_26

theorem contender_23_lt_contender_26 : contender_23 < contender_26 :=
  Nat.lt_trans contender_23_lt_contender_25 contender_25_lt_contender_26

end BusyLean
