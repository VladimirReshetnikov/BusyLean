import BusyLean.Contender34
import BusyLean.Comparison33

/-! # Contender 34: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectTSFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.tsvalue n (packFamily fs) n) (FL.tstreeLadderUpTo n))) :
    m < reflectTSFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectTSFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectTSFamily fs n :=
  lt_reflectTSFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem tsvalue_lt_reflectTSFamily (fs : Family) {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.treeStackedTree n))}
    (ht : t ∈ FL.tstreeLadderUpTo n) :
    FL.tsvalue n (packFamily fs) n t < reflectTSFamily fs n :=
  lt_reflectTSFamily
    (Nat.le_trans (le_maximum (FL.tsvalue n (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem tsTransformer_progressive : Progressive tsTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectTSFamily seed hi

/-- At every input, `F34` exceeds Contender 33's family. -/
theorem family33_lt_F34 (n : Nat) : family33 n < F34 n :=
  ((wDiagonalLift_preservesProgressive (schedule34 n) (rank34 n))
    tsTransformer tsTransformer_progressive)
    (fun _ => family33) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F34 (n : Nat) : reflectTSFamily (fun _ => family33) n < F34 n :=
  (wDiagonalLift_strictlyInflationary (schedule34 n) (rank34 n))
    tsTransformer tsTransformer_progressive (fun _ => family33) n n n (Nat.le_refl n)

/-- Every program of depth `≤ n` over the addresses of `treeStackedTree n`, run with the
packed seed, is below `F34 n`. -/
theorem tsvalue_lt_F34 {n : Nat} {t : FL.CTm (Ordinal.Addr (Ordinal.treeStackedTree n))}
    (ht : t ∈ FL.tstreeLadderUpTo n) :
    FL.tsvalue n (packFamily (fun _ => family33)) n t < F34 n :=
  Nat.lt_trans (tsvalue_lt_reflectTSFamily (fun _ => family33) ht) (raw_reflection_lt_F34 n)

theorem input_lt_family33 (n : Nat) : n < family33 n :=
  Nat.lt_trans (input_lt_F33 n) (input_lt_F33 (F33 n))

theorem input_lt_F34 (n : Nat) : n < F34 n :=
  Nat.lt_trans (input_lt_family33 n) (family33_lt_F34 n)

/-- **The required comparison**: Contender 33 is strictly smaller than Contender 34. -/
theorem contender_33_lt_contender_34 : contender_33 < contender_34 :=
  Nat.lt_trans (family33_lt_F34 42) (input_lt_F34 (F34 42))

theorem contender_32_lt_contender_34 : contender_32 < contender_34 :=
  Nat.lt_trans contender_32_lt_contender_33 contender_33_lt_contender_34

end BusyLean
