import BusyLean.Contender30
import BusyLean.Comparison29

/-! # Contender 30: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectTLFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.tlvalue n (packFamily fs) n) (FL.tltreeLadderUpTo n))) :
    m < reflectTLFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectTLFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectTLFamily fs n :=
  lt_reflectTLFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem tlvalue_lt_reflectTLFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.typeLevelTree n))}
    (ht : t ∈ FL.tltreeLadderUpTo n) :
    FL.tlvalue n (packFamily fs) n t < reflectTLFamily fs n :=
  lt_reflectTLFamily
    (Nat.le_trans (le_maximum (FL.tlvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem tlTransformer_progressive : Progressive tlTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectTLFamily seed hi

/-- At every input, `F30` exceeds Contender 29's family. -/
theorem family29_lt_F30 (n : Nat) : family29 n < F30 n :=
  ((wDiagonalLift_preservesProgressive (schedule30 n) (rank30 n))
    tlTransformer tlTransformer_progressive)
    (fun _ => family29) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F30 (n : Nat) : reflectTLFamily (fun _ => family29) n < F30 n :=
  (wDiagonalLift_strictlyInflationary (schedule30 n) (rank30 n))
    tlTransformer tlTransformer_progressive (fun _ => family29) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `typeLevelTree n`, run with the
packed seed, is below `F30 n`. -/
theorem tlvalue_lt_F30 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.typeLevelTree n))}
    (ht : t ∈ FL.tltreeLadderUpTo n) :
    FL.tlvalue n (packFamily (fun _ => family29)) n t < F30 n :=
  Nat.lt_trans (tlvalue_lt_reflectTLFamily (fun _ => family29) ht) (raw_reflection_lt_F30 n)

theorem input_lt_family29 (n : Nat) : n < family29 n :=
  Nat.lt_trans (input_lt_F29 n) (input_lt_F29 (F29 n))

theorem input_lt_F30 (n : Nat) : n < F30 n :=
  Nat.lt_trans (input_lt_family29 n) (family29_lt_F30 n)

/-- **The required comparison**: Contender 29 is strictly smaller than Contender 30. -/
theorem contender_29_lt_contender_30 : contender_29 < contender_30 :=
  Nat.lt_trans (family29_lt_F30 42) (input_lt_F30 (F30 42))

theorem contender_28_lt_contender_30 : contender_28 < contender_30 :=
  Nat.lt_trans contender_28_lt_contender_29 contender_29_lt_contender_30

end BusyLean
