import BusyLean.Contender25
import BusyLean.Comparison24

/-! # Contender 25: comparison and domination theorems -/

namespace BusyLean

open BusyLean.W

/-- The old raw round-tower reflection is strictly below the new budget. -/
theorem reflectRFamily_lt_budget25 (fs : Family) (n : Nat) :
    reflectRFamily fs n < budget25 fs n := by
  unfold budget25
  omega

/-- Every visible oracle coordinate is strictly below the reflection-generated
budget. -/
theorem oracle_lt_budget25 (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < budget25 fs n :=
  Nat.lt_trans (oracle_lt_reflectRFamily fs hi)
    (reflectRFamily_lt_budget25 fs n)

/-- The external input is strictly below the reflection-generated budget. -/
theorem input_lt_budget25 (fs : Family) (n : Nat) :
    n < budget25 fs n := by
  unfold budget25
  omega

/-- The selected round/depth/fuel budget is strictly below the new raw
reflection. -/
theorem budget25_lt_reflectRStarFamily (fs : Family) (n : Nat) :
    budget25 fs n < reflectRStarFamily fs n := by
  unfold reflectRStarFamily
  omega

/-- General maximum-to-reflection comparison. -/
theorem lt_reflectRStarFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.rvalue (budget25 fs n) (packFamily fs) (budget25 fs n))
        (FL.roundLadderUpTo (budget25 fs n)))) :
    m < reflectRStarFamily fs n := by
  unfold reflectRStarFamily
  omega

/-- Every visible oracle coordinate is strictly below the new raw reflector. -/
theorem oracle_lt_reflectRStarFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectRStarFamily fs n :=
  lt_reflectRStarFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every accepted program at the reflection-generated round/depth/fuel budget
is below the raw reflector. -/
theorem rStarValue_lt_reflectRStarFamily (fs : Family) {n : Nat}
    {t : FL.CTm ((Ordinal.roundTower (budget25 fs n)).T)}
    (ht : t ∈ FL.roundLadderUpTo (budget25 fs n)) :
    FL.rvalue (budget25 fs n) (packFamily fs) (budget25 fs n) t <
      reflectRStarFamily fs n :=
  lt_reflectRStarFamily
    (Nat.le_trans
      (le_maximum
        (FL.rvalue (budget25 fs n) (packFamily fs) (budget25 fs n)) ht)
      (BigNumber.le_maxN_right _ _))

/-- Reflection-indexed round-tower reflection is progressive. -/
theorem rStarTransformer_progressive : Progressive rStarTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectRStarFamily seed hi

/-- At every input, `F25` exceeds Contender 24's entire family. -/
theorem family24_lt_F25 (n : Nat) : family24 n < F25 n :=
  ((wDiagonalLift_preservesProgressive (schedule25 n) (rank25 n))
    rStarTransformer rStarTransformer_progressive)
    (fun _ => family24) 0 n n (Nat.zero_le n)

/-- The raw reflection-indexed round-tower reflector is strictly below the
W-ranked construction. -/
theorem raw_reflection_lt_F25 (n : Nat) :
    reflectRStarFamily (fun _ => family24) n < F25 n :=
  (wDiagonalLift_strictlyInflationary (schedule25 n) (rank25 n))
    rStarTransformer rStarTransformer_progressive
    (fun _ => family24) n n n (Nat.le_refl n)

/-- The self-selected finite round/depth/fuel budget is strictly below `F25`. -/
theorem height25_lt_F25 (n : Nat) : height25 n < F25 n :=
  Nat.lt_trans
    (budget25_lt_reflectRStarFamily (fun _ => family24) n)
    (raw_reflection_lt_F25 n)

/-- Every accepted program over `roundTower (height25 n)`, at depth and fuel
`height25 n`, is below `F25 n`. -/
theorem rStarValue_lt_F25 {n : Nat}
    {t : FL.CTm ((Ordinal.roundTower (height25 n)).T)}
    (ht : t ∈ FL.roundLadderUpTo (height25 n)) :
    FL.rvalue (height25 n) (packFamily (fun _ => family24)) (height25 n) t <
      F25 n :=
  Nat.lt_trans
    (rStarValue_lt_reflectRStarFamily (fun _ => family24) ht)
    (raw_reflection_lt_F25 n)

/-- At the contest input, the incumbent raw reflector, run with Contender 24's
family as oracle, is already below the new round index. -/
theorem old_raw24_lt_height25_42 :
    reflectRFamily (fun _ => family24) 42 < height25 42 :=
  reflectRFamily_lt_budget25 (fun _ => family24) 42

/-- At the contest input, the new round index strictly exceeds Contender 24. -/
theorem contender_24_lt_height25_42 : contender_24 < height25 42 :=
  oracle_lt_budget25 (fun _ => family24)
    (i := 0) (n := 42) (Nat.zero_le 42)

/-- Contender 24 is below the new raw reflection even before W-ranked
hyperreflection is applied. -/
theorem contender_24_lt_raw25_42 :
    contender_24 < reflectRStarFamily (fun _ => family24) 42 :=
  Nat.lt_trans contender_24_lt_height25_42
    (budget25_lt_reflectRStarFamily (fun _ => family24) 42)

theorem input_lt_family24 (n : Nat) : n < family24 n :=
  Nat.lt_trans (input_lt_F24 n) (input_lt_F24 (F24 n))

theorem input_lt_F25 (n : Nat) : n < F25 n :=
  Nat.lt_trans (input_lt_family24 n) (family24_lt_F25 n)

/-- The complete formal margin at the contest input:

`Contender 24 < selected round < raw new reflection < F25 42 < Contender 25`.
-/
theorem contender_24_lt_selected_F25 : contender_24 < F25 42 :=
  Nat.lt_trans contender_24_lt_raw25_42 (raw_reflection_lt_F25 42)

/-- **The required comparison:** Contender 24 is strictly smaller than
Contender 25. -/
theorem contender_24_lt_contender_25 : contender_24 < contender_25 :=
  Nat.lt_trans (family24_lt_F25 42) (input_lt_F25 (F25 42))

/-- Convenient transitive comparisons with the previous two accepted entries. -/
theorem contender_23_lt_contender_25 : contender_23 < contender_25 :=
  Nat.lt_trans contender_23_lt_contender_24 contender_24_lt_contender_25

theorem contender_22_lt_contender_25 : contender_22 < contender_25 :=
  Nat.lt_trans contender_22_lt_contender_24 contender_24_lt_contender_25

end BusyLean
