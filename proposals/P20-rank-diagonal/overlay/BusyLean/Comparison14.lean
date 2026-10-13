import BusyLean.Contender14
import BusyLean.Comparison13

/-! # Contender 14: comparison theorems -/

namespace BusyLean.Fd

/-- A bound on the reflected finite maximum is strictly exceeded. -/
theorem lt_reflectFamily {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN
      (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (fvalue (BusyLean.packFamily fs) n) (ctmsUpTo n))) :
    m < reflectFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible oracle-family coordinate is exceeded. -/
theorem oracle_lt_reflectFamily (fs : W.Family) {i n : Nat}
    (hi : i ≤ n) : fs i n < reflectFamily fs n :=
  lt_reflectFamily
    (Nat.le_trans (W.le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every enumerated dynamic-kind program is exceeded. -/
theorem fvalue_lt_reflectFamily (fs : W.Family) {n : Nat} {t : CTm}
    (ht : t ∈ ctmsUpTo n) :
    fvalue (BusyLean.packFamily fs) n t < reflectFamily fs n :=
  lt_reflectFamily
    (Nat.le_trans (W.le_maximum (fvalue (BusyLean.packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- The numerical input itself is exceeded. -/
theorem input_lt_reflectFamily (fs : W.Family) (n : Nat) :
    n < reflectFamily fs n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

end BusyLean.Fd

namespace BusyLean

/-- Family-aware dynamic-kind reflection is a progressive transformer. -/
theorem fdFamilyTransformer_progressive :
    Progressive fdFamilyTransformer := by
  intro seed i o n hi
  exact Fd.oracle_lt_reflectFamily seed hi

/-- Contender 13's family lies below the rank-diagonal family at every input. -/
theorem family13_lt_rankFamily14 (n : Nat) :
    family13 n < rankFamily14 n 0 n := by
  change seed13 0 n <
    rankLift (schedule14 n) (diagonalRank14 n)
      fdFamilyTransformer seed13 0 n
  exact
    (rankLift_progressive (schedule14 n) (diagonalRank14 n)
      fdFamilyTransformer_progressive) seed13 0 0 n (Nat.zero_le n)

/-- Every visible coordinate of the rank-diagonal family is below `F14`. -/
theorem rankFamily14_lt_F14 {n i : Nat} (hi : i ≤ n) :
    rankFamily14 n i n < F14 n :=
  Fd.oracle_lt_reflectFamily (rankFamily14 n) hi

/-- Pointwise dominance over Contender 13's complete construction. -/
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n :=
  Nat.lt_trans (family13_lt_rankFamily14 n)
    (rankFamily14_lt_F14 (n := n) (i := 0) (Nat.zero_le n))

/-- `F13` strictly exceeds its input. -/
theorem input_lt_F13 (n : Nat) : n < F13 n :=
  Fd.input_lt_reflectFd family12 n

/-- Contender 13's family strictly exceeds its input. -/
theorem input_lt_family13 (n : Nat) : n < family13 n :=
  Nat.lt_trans (input_lt_F13 n) (input_lt_F13 (F13 n))

/-- The diagonal meta-rank eventually lies above every fixed finite rank. -/
theorem fixed_rank_lt_diagonalRank14 {k n : Nat} (hkn : k ≤ n) :
    k < diagonalRank14 n :=
  Nat.lt_of_le_of_lt hkn
    (Nat.lt_trans (input_lt_family13 n) (Nat.lt_succ_self _))

/-- `F14` strictly exceeds its input. -/
theorem input_lt_F14 (n : Nat) : n < F14 n :=
  Nat.lt_trans (input_lt_family13 n) (family13_lt_F14 n)

/-- **The required comparison:** Contender 13 is strictly below Contender 14. -/
theorem contender_13_lt_contender_14 : contender_13 < contender_14 :=
  Nat.lt_trans (family13_lt_F14 42) (input_lt_F14 (F14 42))

/-- Every dynamic-kind program in the final pointwise reflection is exceeded. -/
theorem fvalue_lt_F14 {n : Nat} {t : Fd.CTm} (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily (rankFamily14 n)) n t < F14 n :=
  Fd.fvalue_lt_reflectFamily (rankFamily14 n) ht

/-- Final-instance form of the preceding program bound. -/
theorem fvalue_lt_contender_14 {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo (F14 42)) :
    Fd.fvalue (packFamily (rankFamily14 (F14 42))) (F14 42) t <
      contender_14 :=
  fvalue_lt_F14 ht

/-- Transitive comparison with Contender 12. -/
theorem contender_12_lt_contender_14 : contender_12 < contender_14 :=
  Nat.lt_trans contender_12_lt_contender_13 contender_13_lt_contender_14

end BusyLean
