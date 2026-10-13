import BusyLean.Contender31
import BusyLean.Comparison30

/-! # Contender 31: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectTTFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.ttvalue n (packFamily fs) n) (FL.tttreeLadderUpTo n))) :
    m < reflectTTFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectTTFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectTTFamily fs n :=
  lt_reflectTTFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem ttvalue_lt_reflectTTFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.transTypeTree n))}
    (ht : t ∈ FL.tttreeLadderUpTo n) :
    FL.ttvalue n (packFamily fs) n t < reflectTTFamily fs n :=
  lt_reflectTTFamily
    (Nat.le_trans (le_maximum (FL.ttvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem ttTransformer_progressive : Progressive ttTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectTTFamily seed hi

/-- At every input, `F31` exceeds Contender 30's family. -/
theorem family30_lt_F31 (n : Nat) : family30 n < F31 n :=
  ((wDiagonalLift_preservesProgressive (schedule31 n) (rank31 n))
    ttTransformer ttTransformer_progressive)
    (fun _ => family30) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F31 (n : Nat) : reflectTTFamily (fun _ => family30) n < F31 n :=
  (wDiagonalLift_strictlyInflationary (schedule31 n) (rank31 n))
    ttTransformer ttTransformer_progressive (fun _ => family30) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `transTypeTree n`, run with the
packed seed, is below `F31 n`. -/
theorem ttvalue_lt_F31 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.transTypeTree n))}
    (ht : t ∈ FL.tttreeLadderUpTo n) :
    FL.ttvalue n (packFamily (fun _ => family30)) n t < F31 n :=
  Nat.lt_trans (ttvalue_lt_reflectTTFamily (fun _ => family30) ht) (raw_reflection_lt_F31 n)

theorem input_lt_family30 (n : Nat) : n < family30 n :=
  Nat.lt_trans (input_lt_F30 n) (input_lt_F30 (F30 n))

theorem input_lt_F31 (n : Nat) : n < F31 n :=
  Nat.lt_trans (input_lt_family30 n) (family30_lt_F31 n)

/-- **The required comparison**: Contender 30 is strictly smaller than Contender 31. -/
theorem contender_30_lt_contender_31 : contender_30 < contender_31 :=
  Nat.lt_trans (family30_lt_F31 42) (input_lt_F31 (F31 42))

theorem contender_29_lt_contender_31 : contender_29 < contender_31 :=
  Nat.lt_trans contender_29_lt_contender_30 contender_30_lt_contender_31

end BusyLean
