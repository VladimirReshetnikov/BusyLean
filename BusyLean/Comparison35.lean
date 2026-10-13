import BusyLean.Contender35
import BusyLean.Comparison34

/-! # Contender 35: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectFTFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.ftvalue n (packFamily fs) n) (FL.ftLadderUpTo n))) :
    m < reflectFTFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectFTFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectFTFamily fs n :=
  lt_reflectFTFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem ftvalue_lt_reflectFTFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (ftTree n))}
    (ht : t ∈ FL.ftLadderUpTo n) :
    FL.ftvalue n (packFamily fs) n t < reflectFTFamily fs n :=
  lt_reflectFTFamily
    (Nat.le_trans (le_maximum (FL.ftvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem ftTransformer_progressive : Progressive ftTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectFTFamily seed hi

/-- At every input, `F35` exceeds Contender 34's family. -/
theorem family34_lt_F35 (n : Nat) : family34 n < F35 n :=
  ((wDiagonalLift_preservesProgressive (schedule35 n) (rank35 n))
    ftTransformer ftTransformer_progressive)
    (fun _ => family34) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F35 (n : Nat) : reflectFTFamily (fun _ => family34) n < F35 n :=
  (wDiagonalLift_strictlyInflationary (schedule35 n) (rank35 n))
    ftTransformer ftTransformer_progressive (fun _ => family34) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `ftTree n`, run with the
packed seed, is below `F35 n`. -/
theorem ftvalue_lt_F35 {n : Nat} {t : FL.CTm (Ordinal.Addr (ftTree n))}
    (ht : t ∈ FL.ftLadderUpTo n) :
    FL.ftvalue n (packFamily (fun _ => family34)) n t < F35 n :=
  Nat.lt_trans (ftvalue_lt_reflectFTFamily (fun _ => family34) ht) (raw_reflection_lt_F35 n)

theorem input_lt_family34 (n : Nat) : n < family34 n :=
  Nat.lt_trans (input_lt_F34 n) (input_lt_F34 (F34 n))

theorem input_lt_F35 (n : Nat) : n < F35 n :=
  Nat.lt_trans (input_lt_family34 n) (family34_lt_F35 n)

/-- **The required comparison**: Contender 34 is strictly smaller than Contender 35. -/
theorem contender_34_lt_contender_35 : contender_34 < contender_35 :=
  Nat.lt_trans (family34_lt_F35 42) (input_lt_F35 (F35 42))

theorem contender_33_lt_contender_35 : contender_33 < contender_35 :=
  Nat.lt_trans contender_33_lt_contender_34 contender_34_lt_contender_35

end BusyLean
