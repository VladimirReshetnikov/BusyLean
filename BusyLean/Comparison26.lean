import BusyLean.Contender26
import BusyLean.Comparison25

/-! # Contender 26: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectLTFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.lvalue26 n (packFamily fs) n) (FL.ltreeLadderUpTo n))) :
    m < reflectLTFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectLTFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectLTFamily fs n :=
  lt_reflectLTFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem lvalue26_lt_reflectLTFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.ladderTree n))}
    (ht : t ∈ FL.ltreeLadderUpTo n) :
    FL.lvalue26 n (packFamily fs) n t < reflectLTFamily fs n :=
  lt_reflectLTFamily
    (Nat.le_trans (le_maximum (FL.lvalue26 n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem ltTransformer_progressive : Progressive ltTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectLTFamily seed hi

/-- At every input, `F26` exceeds Contender 25's family. -/
theorem family25_lt_F26 (n : Nat) : family25 n < F26 n :=
  ((wDiagonalLift_preservesProgressive (schedule26 n) (rank26 n))
    ltTransformer ltTransformer_progressive)
    (fun _ => family25) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F26 (n : Nat) : reflectLTFamily (fun _ => family25) n < F26 n :=
  (wDiagonalLift_strictlyInflationary (schedule26 n) (rank26 n))
    ltTransformer ltTransformer_progressive (fun _ => family25) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `ladderTree n`, run with the
packed seed, is below `F26 n`. -/
theorem lvalue26_lt_F26 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.ladderTree n))}
    (ht : t ∈ FL.ltreeLadderUpTo n) :
    FL.lvalue26 n (packFamily (fun _ => family25)) n t < F26 n :=
  Nat.lt_trans (lvalue26_lt_reflectLTFamily (fun _ => family25) ht) (raw_reflection_lt_F26 n)

theorem input_lt_family25 (n : Nat) : n < family25 n :=
  Nat.lt_trans (input_lt_F25 n) (input_lt_F25 (F25 n))

theorem input_lt_F26 (n : Nat) : n < F26 n :=
  Nat.lt_trans (input_lt_family25 n) (family25_lt_F26 n)

/-- **The required comparison**: Contender 25 is strictly smaller than Contender 26. -/
theorem contender_25_lt_contender_26 : contender_25 < contender_26 :=
  Nat.lt_trans (family25_lt_F26 42) (input_lt_F26 (F26 42))

theorem contender_24_lt_contender_26 : contender_24 < contender_26 :=
  Nat.lt_trans contender_24_lt_contender_25 contender_25_lt_contender_26

end BusyLean
