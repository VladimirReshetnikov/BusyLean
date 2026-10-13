import BusyLean.Contender29
import BusyLean.Comparison28

/-! # Contender 29: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectOTFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.otvalue n (packFamily fs) n) (FL.otreeLadderUpTo n))) :
    m < reflectOTFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectOTFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectOTFamily fs n :=
  lt_reflectOTFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem otvalue_lt_reflectOTFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.operatorTree n))}
    (ht : t ∈ FL.otreeLadderUpTo n) :
    FL.otvalue n (packFamily fs) n t < reflectOTFamily fs n :=
  lt_reflectOTFamily
    (Nat.le_trans (le_maximum (FL.otvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem otTransformer_progressive : Progressive otTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectOTFamily seed hi

/-- At every input, `F29` exceeds Contender 28's family. -/
theorem family28_lt_F29 (n : Nat) : family28 n < F29 n :=
  ((wDiagonalLift_preservesProgressive (schedule29 n) (rank29 n))
    otTransformer otTransformer_progressive)
    (fun _ => family28) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F29 (n : Nat) : reflectOTFamily (fun _ => family28) n < F29 n :=
  (wDiagonalLift_strictlyInflationary (schedule29 n) (rank29 n))
    otTransformer otTransformer_progressive (fun _ => family28) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `operatorTree n`, run with the
packed seed, is below `F29 n`. -/
theorem otvalue_lt_F29 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.operatorTree n))}
    (ht : t ∈ FL.otreeLadderUpTo n) :
    FL.otvalue n (packFamily (fun _ => family28)) n t < F29 n :=
  Nat.lt_trans (otvalue_lt_reflectOTFamily (fun _ => family28) ht) (raw_reflection_lt_F29 n)

theorem input_lt_family28 (n : Nat) : n < family28 n :=
  Nat.lt_trans (input_lt_F28 n) (input_lt_F28 (F28 n))

theorem input_lt_F29 (n : Nat) : n < F29 n :=
  Nat.lt_trans (input_lt_family28 n) (family28_lt_F29 n)

/-- **The required comparison**: Contender 28 is strictly smaller than Contender 29. -/
theorem contender_28_lt_contender_29 : contender_28 < contender_29 :=
  Nat.lt_trans (family28_lt_F29 42) (input_lt_F29 (F29 42))

theorem contender_27_lt_contender_29 : contender_27 < contender_29 :=
  Nat.lt_trans contender_27_lt_contender_28 contender_28_lt_contender_29

end BusyLean
