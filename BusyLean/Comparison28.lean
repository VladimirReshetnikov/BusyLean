import BusyLean.Contender28
import BusyLean.Comparison27

/-! # Contender 28: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectRTFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.rtvalue n (packFamily fs) n) (FL.rtreeLadderUpTo n))) :
    m < reflectRTFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectRTFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectRTFamily fs n :=
  lt_reflectRTFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem rtvalue_lt_reflectRTFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.roundTree n))}
    (ht : t ∈ FL.rtreeLadderUpTo n) :
    FL.rtvalue n (packFamily fs) n t < reflectRTFamily fs n :=
  lt_reflectRTFamily
    (Nat.le_trans (le_maximum (FL.rtvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem rtTransformer_progressive : Progressive rtTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectRTFamily seed hi

/-- At every input, `F28` exceeds Contender 27's family. -/
theorem family27_lt_F28 (n : Nat) : family27 n < F28 n :=
  ((wDiagonalLift_preservesProgressive (schedule28 n) (rank28 n))
    rtTransformer rtTransformer_progressive)
    (fun _ => family27) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F28 (n : Nat) : reflectRTFamily (fun _ => family27) n < F28 n :=
  (wDiagonalLift_strictlyInflationary (schedule28 n) (rank28 n))
    rtTransformer rtTransformer_progressive (fun _ => family27) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `roundTree n`, run with the
packed seed, is below `F28 n`. -/
theorem rtvalue_lt_F28 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.roundTree n))}
    (ht : t ∈ FL.rtreeLadderUpTo n) :
    FL.rtvalue n (packFamily (fun _ => family27)) n t < F28 n :=
  Nat.lt_trans (rtvalue_lt_reflectRTFamily (fun _ => family27) ht) (raw_reflection_lt_F28 n)

theorem input_lt_family27 (n : Nat) : n < family27 n :=
  Nat.lt_trans (input_lt_F27 n) (input_lt_F27 (F27 n))

theorem input_lt_F28 (n : Nat) : n < F28 n :=
  Nat.lt_trans (input_lt_family27 n) (family27_lt_F28 n)

/-- **The required comparison**: Contender 27 is strictly smaller than Contender 28. -/
theorem contender_27_lt_contender_28 : contender_27 < contender_28 :=
  Nat.lt_trans (family27_lt_F28 42) (input_lt_F28 (F28 42))

theorem contender_26_lt_contender_28 : contender_26 < contender_28 :=
  Nat.lt_trans contender_26_lt_contender_27 contender_27_lt_contender_28

end BusyLean
