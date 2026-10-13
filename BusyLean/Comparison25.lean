import BusyLean.Contender25
import BusyLean.Comparison24

/-! # Contender 25: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectAFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.avalue n (packFamily fs) n) (FL.addrLadderUpTo n))) :
    m < reflectAFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectAFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectAFamily fs n :=
  lt_reflectAFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem avalue_lt_reflectAFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.bigTree n))}
    (ht : t ∈ FL.addrLadderUpTo n) :
    FL.avalue n (packFamily fs) n t < reflectAFamily fs n :=
  lt_reflectAFamily
    (Nat.le_trans (le_maximum (FL.avalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem aTransformer_progressive : Progressive aTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectAFamily seed hi

/-- At every input, `F25` exceeds Contender 24's family. -/
theorem family24_lt_F25 (n : Nat) : family24 n < F25 n :=
  ((wDiagonalLift_preservesProgressive (schedule25 n) (rank25 n))
    aTransformer aTransformer_progressive)
    (fun _ => family24) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F25 (n : Nat) : reflectAFamily (fun _ => family24) n < F25 n :=
  (wDiagonalLift_strictlyInflationary (schedule25 n) (rank25 n))
    aTransformer aTransformer_progressive (fun _ => family24) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `bigTree n`, run with the
packed seed, is below `F25 n`. -/
theorem avalue_lt_F25 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.bigTree n))}
    (ht : t ∈ FL.addrLadderUpTo n) :
    FL.avalue n (packFamily (fun _ => family24)) n t < F25 n :=
  Nat.lt_trans (avalue_lt_reflectAFamily (fun _ => family24) ht) (raw_reflection_lt_F25 n)

theorem input_lt_family24 (n : Nat) : n < family24 n :=
  Nat.lt_trans (input_lt_F24 n) (input_lt_F24 (F24 n))

theorem input_lt_F25 (n : Nat) : n < F25 n :=
  Nat.lt_trans (input_lt_family24 n) (family24_lt_F25 n)

/-- **The required comparison**: Contender 24 is strictly smaller than Contender 25. -/
theorem contender_24_lt_contender_25 : contender_24 < contender_25 :=
  Nat.lt_trans (family24_lt_F25 42) (input_lt_F25 (F25 42))

theorem contender_23_lt_contender_25 : contender_23 < contender_25 :=
  Nat.lt_trans contender_23_lt_contender_24 contender_24_lt_contender_25

end BusyLean
