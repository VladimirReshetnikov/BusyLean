import BusyLean.Contender36
import BusyLean.Comparison35

/-! # Contender 36: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectBTFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.btvalue n (packFamily fs) n) (FL.btLadderUpTo n))) :
    m < reflectBTFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectBTFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectBTFamily fs n :=
  lt_reflectBTFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem btvalue_lt_reflectBTFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (bootTree n))}
    (ht : t ∈ FL.btLadderUpTo n) :
    FL.btvalue n (packFamily fs) n t < reflectBTFamily fs n :=
  lt_reflectBTFamily
    (Nat.le_trans (le_maximum (FL.btvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem btTransformer_progressive : Progressive btTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectBTFamily seed hi

/-- At every input, `F36` exceeds Contender 35's family. -/
theorem family35_lt_F36 (n : Nat) : family35 n < F36 n :=
  ((wDiagonalLift_preservesProgressive (schedule36 n) (rank36 n))
    btTransformer btTransformer_progressive)
    (fun _ => family35) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F36 (n : Nat) : reflectBTFamily (fun _ => family35) n < F36 n :=
  (wDiagonalLift_strictlyInflationary (schedule36 n) (rank36 n))
    btTransformer btTransformer_progressive (fun _ => family35) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `bootTree n`, run with the
packed seed, is below `F36 n`. -/
theorem btvalue_lt_F36 {n : Nat} {t : FL.CTm (Ordinal.Addr (bootTree n))}
    (ht : t ∈ FL.btLadderUpTo n) :
    FL.btvalue n (packFamily (fun _ => family35)) n t < F36 n :=
  Nat.lt_trans (btvalue_lt_reflectBTFamily (fun _ => family35) ht) (raw_reflection_lt_F36 n)

theorem input_lt_family35 (n : Nat) : n < family35 n :=
  Nat.lt_trans (input_lt_F35 n) (input_lt_F35 (F35 n))

theorem input_lt_F36 (n : Nat) : n < F36 n :=
  Nat.lt_trans (input_lt_family35 n) (family35_lt_F36 n)

/-- **The required comparison**: Contender 35 is strictly smaller than Contender 36. -/
theorem contender_35_lt_contender_36 : contender_35 < contender_36 :=
  Nat.lt_trans (family35_lt_F36 42) (input_lt_F36 (F36 42))

theorem contender_34_lt_contender_36 : contender_34 < contender_36 :=
  Nat.lt_trans contender_34_lt_contender_35 contender_35_lt_contender_36

end BusyLean
