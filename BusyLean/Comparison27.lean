import BusyLean.Contender27
import BusyLean.Comparison26

/-! # Contender 27: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectUFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.uvalue n (packFamily fs) n) (FL.utreeLadderUpTo n))) :
    m < reflectUFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectUFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectUFamily fs n :=
  lt_reflectUFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem uvalue_lt_reflectUFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.universeLadderTree n))}
    (ht : t ∈ FL.utreeLadderUpTo n) :
    FL.uvalue n (packFamily fs) n t < reflectUFamily fs n :=
  lt_reflectUFamily
    (Nat.le_trans (le_maximum (FL.uvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem uTransformer_progressive : Progressive uTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectUFamily seed hi

/-- At every input, `F27` exceeds Contender 26's family. -/
theorem family26_lt_F27 (n : Nat) : family26 n < F27 n :=
  ((wDiagonalLift_preservesProgressive (schedule27 n) (rank27 n))
    uTransformer uTransformer_progressive)
    (fun _ => family26) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F27 (n : Nat) : reflectUFamily (fun _ => family26) n < F27 n :=
  (wDiagonalLift_strictlyInflationary (schedule27 n) (rank27 n))
    uTransformer uTransformer_progressive (fun _ => family26) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `universeLadderTree n`, run with the
packed seed, is below `F27 n`. -/
theorem uvalue_lt_F27 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.universeLadderTree n))}
    (ht : t ∈ FL.utreeLadderUpTo n) :
    FL.uvalue n (packFamily (fun _ => family26)) n t < F27 n :=
  Nat.lt_trans (uvalue_lt_reflectUFamily (fun _ => family26) ht) (raw_reflection_lt_F27 n)

theorem input_lt_family26 (n : Nat) : n < family26 n :=
  Nat.lt_trans (input_lt_F26 n) (input_lt_F26 (F26 n))

theorem input_lt_F27 (n : Nat) : n < F27 n :=
  Nat.lt_trans (input_lt_family26 n) (family26_lt_F27 n)

/-- **The required comparison**: Contender 26 is strictly smaller than Contender 27. -/
theorem contender_26_lt_contender_27 : contender_26 < contender_27 :=
  Nat.lt_trans (family26_lt_F27 42) (input_lt_F27 (F27 42))

theorem contender_25_lt_contender_27 : contender_25 < contender_27 :=
  Nat.lt_trans contender_25_lt_contender_26 contender_26_lt_contender_27

end BusyLean
