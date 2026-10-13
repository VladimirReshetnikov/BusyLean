import BusyLean.Contender32
import BusyLean.Comparison31

/-! # Contender 32: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectLGFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.lgvalue n (packFamily fs) n) (FL.lgtreeLadderUpTo n))) :
    m < reflectLGFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectLGFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectLGFamily fs n :=
  lt_reflectLGFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem lgvalue_lt_reflectLGFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.languageTree n))}
    (ht : t ∈ FL.lgtreeLadderUpTo n) :
    FL.lgvalue n (packFamily fs) n t < reflectLGFamily fs n :=
  lt_reflectLGFamily
    (Nat.le_trans (le_maximum (FL.lgvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem lgTransformer_progressive : Progressive lgTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectLGFamily seed hi

/-- At every input, `F32` exceeds Contender 31's family. -/
theorem family31_lt_F32 (n : Nat) : family31 n < F32 n :=
  ((wDiagonalLift_preservesProgressive (schedule32 n) (rank32 n))
    lgTransformer lgTransformer_progressive)
    (fun _ => family31) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F32 (n : Nat) : reflectLGFamily (fun _ => family31) n < F32 n :=
  (wDiagonalLift_strictlyInflationary (schedule32 n) (rank32 n))
    lgTransformer lgTransformer_progressive (fun _ => family31) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `languageTree n`, run with the
packed seed, is below `F32 n`. -/
theorem lgvalue_lt_F32 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.languageTree n))}
    (ht : t ∈ FL.lgtreeLadderUpTo n) :
    FL.lgvalue n (packFamily (fun _ => family31)) n t < F32 n :=
  Nat.lt_trans (lgvalue_lt_reflectLGFamily (fun _ => family31) ht) (raw_reflection_lt_F32 n)

theorem input_lt_family31 (n : Nat) : n < family31 n :=
  Nat.lt_trans (input_lt_F31 n) (input_lt_F31 (F31 n))

theorem input_lt_F32 (n : Nat) : n < F32 n :=
  Nat.lt_trans (input_lt_family31 n) (family31_lt_F32 n)

/-- **The required comparison**: Contender 31 is strictly smaller than Contender 32. -/
theorem contender_31_lt_contender_32 : contender_31 < contender_32 :=
  Nat.lt_trans (family31_lt_F32 42) (input_lt_F32 (F32 42))

theorem contender_30_lt_contender_32 : contender_30 < contender_32 :=
  Nat.lt_trans contender_30_lt_contender_31 contender_31_lt_contender_32

end BusyLean
