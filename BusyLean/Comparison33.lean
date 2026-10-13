import BusyLean.Contender33
import BusyLean.Comparison32

/-! # Contender 33: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectSKFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.skvalue n (packFamily fs) n) (FL.sktreeLadderUpTo n))) :
    m < reflectSKFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectSKFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectSKFamily fs n :=
  lt_reflectSKFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem skvalue_lt_reflectSKFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.stackedTree n))}
    (ht : t ∈ FL.sktreeLadderUpTo n) :
    FL.skvalue n (packFamily fs) n t < reflectSKFamily fs n :=
  lt_reflectSKFamily
    (Nat.le_trans (le_maximum (FL.skvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem skTransformer_progressive : Progressive skTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectSKFamily seed hi

/-- At every input, `F33` exceeds Contender 32's family. -/
theorem family32_lt_F33 (n : Nat) : family32 n < F33 n :=
  ((wDiagonalLift_preservesProgressive (schedule33 n) (rank33 n))
    skTransformer skTransformer_progressive)
    (fun _ => family32) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F33 (n : Nat) : reflectSKFamily (fun _ => family32) n < F33 n :=
  (wDiagonalLift_strictlyInflationary (schedule33 n) (rank33 n))
    skTransformer skTransformer_progressive (fun _ => family32) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `stackedTree n`, run with the
packed seed, is below `F33 n`. -/
theorem skvalue_lt_F33 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.stackedTree n))}
    (ht : t ∈ FL.sktreeLadderUpTo n) :
    FL.skvalue n (packFamily (fun _ => family32)) n t < F33 n :=
  Nat.lt_trans (skvalue_lt_reflectSKFamily (fun _ => family32) ht) (raw_reflection_lt_F33 n)

theorem input_lt_family32 (n : Nat) : n < family32 n :=
  Nat.lt_trans (input_lt_F32 n) (input_lt_F32 (F32 n))

theorem input_lt_F33 (n : Nat) : n < F33 n :=
  Nat.lt_trans (input_lt_family32 n) (family32_lt_F33 n)

/-- **The required comparison**: Contender 32 is strictly smaller than Contender 33. -/
theorem contender_32_lt_contender_33 : contender_32 < contender_33 :=
  Nat.lt_trans (family32_lt_F33 42) (input_lt_F33 (F33 42))

theorem contender_31_lt_contender_33 : contender_31 < contender_33 :=
  Nat.lt_trans contender_31_lt_contender_32 contender_32_lt_contender_33

end BusyLean
