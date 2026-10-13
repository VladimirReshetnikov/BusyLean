import BusyLean.Contender14
import BusyLean.Comparison13
import BusyLean.MetaReflectionFacts
import BusyLean.ReflectionFacts

/-!
# Contender 14: comparison and domination theorems

No monotonicity of reflection in its oracle is used.  Every strict inequality
is obtained from one of three explicit occurrences:

1. a visible coordinate in `reflect14`'s prefix maximum;
2. a visible child of the crowned operator tree;
3. a visible seed coordinate of a progressive transformer.
-/

namespace BusyLean

/-- A number bounded by `reflect14`'s displayed maximum is strictly below the
reflection result. -/
theorem lt_reflect14 {fs : W.Family} {n m : Nat}
    (h : m ≤
      BigNumber.maxN
        (W.prefixMax (fun i => fs i n) n)
        (BigNumber.maximum (Fd.fvalue (packFamily fs) n) (Fd.ctmsUpTo n))) :
    m < reflect14 fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible oracle-family coordinate is exceeded. -/
theorem oracle_lt_reflect14 (fs : W.Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflect14 fs n :=
  lt_reflect14
    (Nat.le_trans
      (W.le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every accepted dynamic-kind program in the finite syntax budget is
exceeded when run with the packed family oracle. -/
theorem fvalue_lt_reflect14 (fs : W.Family) {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily fs) n t < reflect14 fs n :=
  lt_reflect14
    (Nat.le_trans
      (W.le_maximum (Fd.fvalue (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- The numerical input is exceeded. -/
theorem input_lt_reflect14 (fs : W.Family) (n : Nat) :
    n < reflect14 fs n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

/-- Family-aware dynamic-kind reflection is progressive. -/
theorem fdTransformer14_progressive : Progressive fdTransformer14 := by
  intro seed i o n hi
  exact oracle_lt_reflect14 seed hi

/-- Every finite metalevel is progressive. -/
theorem metaTower14_progressive : ∀ k, Progressive (metaTower14 k)
  | 0 => fdTransformer14_progressive
  | k + 1 => by
      simpa [metaTower14, metaStep14] using
        (operatorStage_progressive (metaTower14 k)
          (metaTower14_progressive k) tree14)

/-- A single crowned metastep strictly dominates its input transformer at every
visible coordinate.  The proof follows the explicit path

`op -> liftTransformer op = operatorStage op leaf -> tree14.child(0) -> tree14`.
-/
theorem transformer_lt_metaStep14 {op : Transformer}
    (hop : Progressive op) (seed : W.Family) {i o n : Nat} (hi : i ≤ n) :
    op seed i n < metaStep14 op seed o n := by
  have hLift : op seed i n < liftTransformer op seed 0 n :=
    transformer_lt_lift_at hop seed hi
  have hLeaf :
      op seed i n < operatorStage op (.leaf) seed 0 n := by
    simpa [operatorStage] using hLift
  have hCrownRaw :=
    operatorStage_child_lt op hop seed (crown14 coreTree14)
      (i := 0) (o := o) (n := n) (Nat.zero_le n)
  have hCrown :
      operatorStage op (.leaf) seed 0 n <
        operatorStage op tree14 seed o n := by
    simpa [tree14, crown14] using hCrownRaw
  exact Nat.lt_trans hLeaf (by simpa [metaStep14] using hCrown)

/-- The nontrivial core of any crowned schedule is a visible child of the
parent operator stage.  Instantiating `core := coreTree14` proves that the large
autonomous schedule used by Contender 14 is mathematically relevant rather than
decorative. -/
theorem coreStage_lt_crowned14 {op : Transformer}
    (hop : Progressive op) (core : BigNumber.WTree Nat) (seed : W.Family)
    {o n : Nat} (h1 : 1 ≤ n) :
    operatorStage op core seed 0 n <
      operatorStage op (.node (crown14 core)) seed o n := by
  have hCore :=
    operatorStage_child_lt op hop seed (crown14 core)
      (i := 1) (o := o) (n := n) h1
  simpa [crown14] using hCore

/-- Successive metalevels are strictly increasing at every visible input
coordinate. -/
theorem metaTower14_step_lt (k : Nat) (seed : W.Family)
    {i o n : Nat} (hi : i ≤ n) :
    metaTower14 k seed i n < metaTower14 (k + 1) seed o n := by
  simpa [metaTower14] using
    (transformer_lt_metaStep14 (metaTower14_progressive k) seed hi)

/-- The base dynamic-kind transformer is below every positive metalevel. -/
theorem fdTransformer14_lt_metaTower14_succ
    (k : Nat) (seed : W.Family) {i o n : Nat} (hi : i ≤ n) :
    fdTransformer14 seed i n < metaTower14 (k + 1) seed o n := by
  induction k generalizing o with
  | zero =>
      simpa [metaTower14] using
        (transformer_lt_metaStep14 fdTransformer14_progressive seed
          (i := i) (o := o) (n := n) hi)
  | succ k ih =>
      have hBase :
          fdTransformer14 seed i n < metaTower14 (k + 1) seed 0 n :=
        ih (o := 0)
      have hStep :
          metaTower14 (k + 1) seed 0 n <
            metaTower14 ((k + 1) + 1) seed o n :=
        metaTower14_step_lt (k + 1) seed (i := 0) (o := o) (n := n)
          (Nat.zero_le n)
      exact Nat.lt_trans hBase hStep

/-- Contender 13's family is beaten pointwise by `F14`. -/
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n := by
  have h :=
    metaTower14_progressive (ramification14 n + 1)
      seed13 0 n n (Nat.zero_le n)
  simpa [F14, seed13] using h

/-- The base family-aware dynamic-kind reflection is already strictly below
`F14`; hence the construction performs genuine operator-level amplification. -/
theorem reflect14_lt_F14 (n : Nat) : reflect14 seed13 n < F14 n := by
  have h :=
    fdTransformer14_lt_metaTower14_succ (ramification14 n) seed13
      (i := 0) (o := n) (n := n) (Nat.zero_le n)
  simpa [F14, fdTransformer14] using h

/-- Every finite-budget dynamic-kind program using the Contender-13 family is
pointwise below `F14`. -/
theorem fvalue_lt_F14 {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily seed13) n t < F14 n :=
  Nat.lt_trans (fvalue_lt_reflect14 seed13 ht) (reflect14_lt_F14 n)

/-- `F13` exceeds its input. -/
theorem input_lt_F13 (n : Nat) : n < F13 n :=
  Fd.input_lt_reflectFd family12 n

/-- Contender 13's family exceeds its input. -/
theorem input_lt_family13 (n : Nat) : n < family13 n := by
  simpa [family13] using
    (Nat.lt_trans (input_lt_F13 n) (input_lt_F13 (F13 n)))

/-- `F14` exceeds its input. -/
theorem input_lt_F14 (n : Nat) : n < F14 n :=
  Nat.lt_trans (input_lt_family13 n) (family13_lt_F14 n)

/-- Contender 13 is definitionally the value `family13 42`. -/
theorem contender_13_eq_family13_42 : contender_13 = family13 42 := rfl

/-- The previous contender is already below the un-diagonalized `F14 42`. -/
theorem contender_13_lt_F14_42 : contender_13 < F14 42 := by
  simpa [contender_13_eq_family13_42] using family13_lt_F14 42

/-- **The required comparison:** Contender 13 is strictly smaller than
Contender 14. -/
theorem contender_13_lt_contender_14 : contender_13 < contender_14 :=
  Nat.lt_trans contender_13_lt_F14_42 (input_lt_F14 (F14 42))

/-- A transitive comparison with Contender 12. -/
theorem contender_12_lt_contender_14 : contender_12 < contender_14 :=
  Nat.lt_trans contender_12_lt_contender_13 contender_13_lt_contender_14

/-- Every dynamic-kind program in the final syntax budget is exceeded by the
final contender. -/
theorem fvalue_lt_contender_14 {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo (F14 42)) :
    Fd.fvalue (packFamily seed13) (F14 42) t < contender_14 :=
  fvalue_lt_F14 ht

end BusyLean
