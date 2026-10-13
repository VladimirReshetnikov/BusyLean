import BusyLean.Contender15
import BusyLean.Comparison14
import BusyLean.HyperReflectionFacts
import BusyLean.MetaReflectionFacts

/-!
# Contender 15: comparison and domination theorems

The proof has two independent strict-growth mechanisms:

1. diagonal hyperreflection strictly exceeds its progressive base transformer;
2. every crowned operator metastep strictly exceeds its input transformer.

The previous contender is used through `F14`, never through the named constant
`contender_14` in the new definition.
-/

namespace BusyLean

/-- The input-sensitive diagonal transformer is progressive. -/
theorem diagonalTransformer15_progressive :
    Progressive diagonalTransformer15 := by
  intro seed i o n hi
  have h :=
    ((diagonalLift_preservesProgressive (schedule15 n) (rank15 n))
      fdFamilyTransformer fdFamilyTransformer_progressive)
      seed i o n hi
  simpa [diagonalTransformer15] using h

/-- At each numerical input, the diagonal transformer strictly exceeds its raw
family-reflection base. -/
theorem fdFamilyTransformer_lt_diagonalTransformer15
    (seed : W.Family) {i o n : Nat} (hi : i ≤ n) :
    fdFamilyTransformer seed i n < diagonalTransformer15 seed o n := by
  have h :=
    (diagonalLift_strictlyInflationary (schedule15 n) (rank15 n))
      fdFamilyTransformer fdFamilyTransformer_progressive seed i o n hi
  simpa [diagonalTransformer15] using h

/-- Every finite operator metalevel is progressive. -/
theorem metaTower15_progressive : ∀ k, Progressive (metaTower15 k)
  | 0 => diagonalTransformer15_progressive
  | k + 1 => by
      simpa [metaTower15, metaStep15] using
        (operatorStage_progressive (metaTower15 k)
          (metaTower15_progressive k) tree15)

/-- A crowned metastep strictly dominates its input transformer at every
visible coordinate. -/
theorem transformer_lt_metaStep15 {op : Transformer}
    (hop : Progressive op) (seed : W.Family) {i o n : Nat} (hi : i ≤ n) :
    op seed i n < metaStep15 op seed o n := by
  have hLift : op seed i n < liftTransformer op seed 0 n :=
    transformer_lt_lift_at hop seed hi
  have hLeaf :
      op seed i n < operatorStage op (.leaf) seed 0 n := by
    simpa [operatorStage] using hLift
  have hCrownRaw :=
    operatorStage_child_lt op hop seed (crown15 coreTree15)
      (i := 0) (o := o) (n := n) (Nat.zero_le n)
  have hCrown :
      operatorStage op (.leaf) seed 0 n <
        operatorStage op tree15 seed o n := by
    simpa [tree15, crown15] using hCrownRaw
  exact Nat.lt_trans hLeaf (by simpa [metaStep15] using hCrown)

/-- The nontrivial core of any crowned Contender-15 schedule is a visible child
of its parent operator stage. -/
theorem coreStage_lt_crowned15 {op : Transformer}
    (hop : Progressive op) (core : BigNumber.WTree Nat) (seed : W.Family)
    {o n : Nat} (h1 : 1 ≤ n) :
    operatorStage op core seed 0 n <
      operatorStage op (.node (crown15 core)) seed o n := by
  have hCore :=
    operatorStage_child_lt op hop seed (crown15 core)
      (i := 1) (o := o) (n := n) h1
  simpa [crown15] using hCore

/-- Successive complete operator metalevels are strictly increasing. -/
theorem metaTower15_step_lt (k : Nat) (seed : W.Family)
    {i o n : Nat} (hi : i ≤ n) :
    metaTower15 k seed i n < metaTower15 (k + 1) seed o n := by
  simpa [metaTower15] using
    (transformer_lt_metaStep15 (metaTower15_progressive k) seed hi)

/-- The diagonal-hyperreflection base is below every positive operator
metalevel. -/
theorem diagonalTransformer15_lt_metaTower15_succ
    (k : Nat) (seed : W.Family) {i o n : Nat} (hi : i ≤ n) :
    diagonalTransformer15 seed i n < metaTower15 (k + 1) seed o n := by
  induction k generalizing o with
  | zero =>
      simpa [metaTower15] using
        (transformer_lt_metaStep15 diagonalTransformer15_progressive seed
          (i := i) (o := o) (n := n) hi)
  | succ k ih =>
      have hBase :
          diagonalTransformer15 seed i n < metaTower15 (k + 1) seed 0 n :=
        ih (o := 0)
      have hStep :
          metaTower15 (k + 1) seed 0 n <
            metaTower15 ((k + 1) + 1) seed o n :=
        metaTower15_step_lt (k + 1) seed
          (i := 0) (o := o) (n := n) (Nat.zero_le n)
      exact Nat.lt_trans hBase hStep

/-- The complete Contender-14 family is pointwise below `F15`. -/
theorem family14_lt_F15 (n : Nat) : family14 n < F15 n := by
  have h :=
    metaTower15_progressive (ramification15 n + 1)
      seed14 0 n n (Nat.zero_le n)
  simpa [F15, seed14] using h

/-- Even the new diagonal-hyperreflection base transformer is strictly below
`F15`, so the outer operator ramification is genuine. -/
theorem diagonalTransformer15_lt_F15 (n : Nat) :
    diagonalTransformer15 seed14 n n < F15 n := by
  have h :=
    diagonalTransformer15_lt_metaTower15_succ (ramification15 n) seed14
      (i := n) (o := n) (n := n) (Nat.le_refl n)
  simpa [F15] using h

/-- Incoming Contender 14's pointwise family is already strictly below the
seed family used by Contender 15. -/
theorem F14_lt_family14 (n : Nat) : F14 n < family14 n := by
  simpa [family14] using input_lt_F14 (F14 n)

/-- Hence the incoming diagonal-hyperreflection family is pointwise below the
new family. -/
theorem F14_lt_F15 (n : Nat) : F14 n < F15 n :=
  Nat.lt_trans (F14_lt_family14 n) (family14_lt_F15 n)

/-- The raw family reflection over the Contender-14 seed lies below the new
input-sensitive diagonal transformer. -/
theorem reflectFdFamily_lt_diagonalTransformer15 (n : Nat) :
    reflectFdFamily seed14 n < diagonalTransformer15 seed14 n n := by
  have h :=
    fdFamilyTransformer_lt_diagonalTransformer15 seed14
      (i := n) (o := n) (n := n) (Nat.le_refl n)
  simpa [fdFamilyTransformer] using h

/-- Every dynamic-kind program in the current finite syntax budget, using the
packed Contender-14 family, is pointwise below `F15`. -/
theorem fvalue_lt_F15 {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily seed14) n t < F15 n :=
  Nat.lt_trans (fvalue_lt_reflectFdFamily seed14 ht)
    (Nat.lt_trans (reflectFdFamily_lt_diagonalTransformer15 n)
      (diagonalTransformer15_lt_F15 n))

/-- The complete Contender-14 family grows past its input. -/
theorem input_lt_family14 (n : Nat) : n < family14 n := by
  simpa [family14] using
    (Nat.lt_trans (input_lt_F14 n) (input_lt_F14 (F14 n)))

/-- `F15` grows past its input. -/
theorem input_lt_F15 (n : Nat) : n < F15 n :=
  Nat.lt_trans (input_lt_family14 n) (family14_lt_F15 n)

/-- Incoming Contender 14 is definitionally `family14 42`. -/
theorem contender_14_eq_family14_42 : contender_14 = family14 42 := rfl

/-- The incoming contender is below the un-diagonalized `F15 42`. -/
theorem contender_14_lt_F15_42 : contender_14 < F15 42 := by
  rw [contender_14_eq_family14_42]
  exact family14_lt_F15 42

/-- **The required superseding comparison:** the incoming diagonal
hyperreflection contender is strictly below Contender 15. -/
theorem contender_14_lt_contender_15 : contender_14 < contender_15 :=
  Nat.lt_trans contender_14_lt_F15_42 (input_lt_F15 (F15 42))

/-- The current accepted Contender 13 is therefore also strictly below
Contender 15. -/
theorem contender_13_lt_contender_15 : contender_13 < contender_15 :=
  Nat.lt_trans contender_13_lt_contender_14 contender_14_lt_contender_15

/-- Every dynamic-kind program in the final syntax budget is below the final
contender. -/
theorem fvalue_lt_contender_15 {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo (F15 42)) :
    Fd.fvalue (packFamily seed14) (F15 42) t < contender_15 :=
  fvalue_lt_F15 ht

end BusyLean
