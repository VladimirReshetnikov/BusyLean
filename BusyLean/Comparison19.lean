import BusyLean.Contender19
import BusyLean.Comparison18

/-! # Contender 19: comparison theorems -/

namespace BusyLean

open BusyLean.W

theorem lt_reflectLFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.lvalue (packFamily fs) n) (FL.lveblenLadderUpTo n))) :
    m < reflectLFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_reflectLFamily (fs : Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflectLFamily fs n :=
  lt_reflectLFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem lvalue_lt_reflectLFamily (fs : Family) {n : Nat} {t : FL.CTm Ordinal.LargeVeblen}
    (ht : t ∈ FL.lveblenLadderUpTo n) :
    FL.lvalue (packFamily fs) n t < reflectLFamily fs n :=
  lt_reflectLFamily
    (Nat.le_trans (le_maximum (FL.lvalue (packFamily fs) n) ht) (BigNumber.le_maxN_right _ _))

theorem lTransformer_progressive : Progressive lTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectLFamily seed hi

/-- At every input, `F19` exceeds Contender 18's family. -/
theorem family18_lt_F19 (n : Nat) : family18 n < F19 n :=
  ((diagonalLift_preservesProgressive (schedule19 n) (rank19 n))
    lTransformer lTransformer_progressive)
    (fun _ => family18) 0 n n (Nat.zero_le n)

theorem raw_reflection_lt_F19 (n : Nat) : reflectLFamily (fun _ => family18) n < F19 n :=
  (diagonalLift_strictlyInflationary (schedule19 n) (rank19 n))
    lTransformer lTransformer_progressive (fun _ => family18) n n n (Nat.le_refl n)

/-- Every Veblen-ladder program of depth `≤ n`, run with the packed seed,
is below `F19 n`. -/
theorem lvalue_lt_F19 {n : Nat} {t : FL.CTm Ordinal.LargeVeblen} (ht : t ∈ FL.lveblenLadderUpTo n) :
    FL.lvalue (packFamily (fun _ => family18)) n t < F19 n :=
  Nat.lt_trans (lvalue_lt_reflectLFamily (fun _ => family18) ht) (raw_reflection_lt_F19 n)

theorem input_lt_family18 (n : Nat) : n < family18 n :=
  Nat.lt_trans (input_lt_F18 n) (input_lt_F18 (F18 n))

theorem input_lt_F19 (n : Nat) : n < F19 n :=
  Nat.lt_trans (input_lt_family18 n) (family18_lt_F19 n)

/-- **The required comparison**: Contender 18 is strictly smaller than Contender 19. -/
theorem contender_18_lt_contender_19 : contender_18 < contender_19 :=
  Nat.lt_trans (family18_lt_F19 42) (input_lt_F19 (F19 42))

theorem contender_17_lt_contender_19 : contender_17 < contender_19 :=
  Nat.lt_trans contender_17_lt_contender_18 contender_18_lt_contender_19

end BusyLean
