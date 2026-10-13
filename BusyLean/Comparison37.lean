import BusyLean.Contender37
import BusyLean.Comparison36

/-! # Contender 37: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectJTFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.jtvalue n (packFamily fs) n) (FL.jtLadderUpTo n))) :
    m < reflectJTFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectJTFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectJTFamily fs n :=
  lt_reflectJTFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem jtvalue_lt_reflectJTFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (jumpTree n))}
    (ht : t ∈ FL.jtLadderUpTo n) :
    FL.jtvalue n (packFamily fs) n t < reflectJTFamily fs n :=
  lt_reflectJTFamily
    (Nat.le_trans (le_maximum (FL.jtvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem jtTransformer_progressive : Progressive jtTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectJTFamily seed hi

/-- At every input, `F37` exceeds Contender 36's family. -/
theorem family36_lt_F37 (n : Nat) : family36 n < F37 n :=
  ((wDiagonalLift_preservesProgressive (schedule37 n) (rank37 n))
    jtTransformer jtTransformer_progressive)
    (fun _ => family36) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F37 (n : Nat) : reflectJTFamily (fun _ => family36) n < F37 n :=
  (wDiagonalLift_strictlyInflationary (schedule37 n) (rank37 n))
    jtTransformer jtTransformer_progressive (fun _ => family36) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `jumpTree n`, run with the
packed seed, is below `F37 n`. -/
theorem jtvalue_lt_F37 {n : Nat} {t : FL.CTm (Ordinal.Addr (jumpTree n))}
    (ht : t ∈ FL.jtLadderUpTo n) :
    FL.jtvalue n (packFamily (fun _ => family36)) n t < F37 n :=
  Nat.lt_trans (jtvalue_lt_reflectJTFamily (fun _ => family36) ht) (raw_reflection_lt_F37 n)

theorem input_lt_family36 (n : Nat) : n < family36 n :=
  Nat.lt_trans (input_lt_F36 n) (input_lt_F36 (F36 n))

theorem input_lt_F37 (n : Nat) : n < F37 n :=
  Nat.lt_trans (input_lt_family36 n) (family36_lt_F37 n)

/-- **The required comparison**: Contender 36 is strictly smaller than Contender 37. -/
theorem contender_36_lt_contender_37 : contender_36 < contender_37 :=
  Nat.lt_trans (family36_lt_F37 42) (input_lt_F37 (F37 42))

theorem contender_35_lt_contender_37 : contender_35 < contender_37 :=
  Nat.lt_trans contender_35_lt_contender_36 contender_36_lt_contender_37

end BusyLean
