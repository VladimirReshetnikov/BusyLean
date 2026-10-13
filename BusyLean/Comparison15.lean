import BusyLean.Contender15
import BusyLean.Comparison14
import BusyLean.HyperReflectionFacts
import BusyLean.MetaReflectionFacts

/-! # Contender 15: universal-envelope comparison theorems -/

namespace BusyLean

/-! ## The universal incoming-candidate envelope -/

theorem diagonalHyper14Family_le_envelope (n : Nat) :
    diagonalHyper14Family n ≤ incoming14Envelope n :=
  BigNumber.le_maxN_left _ _

theorem diagonalOperatorTower14Family_le_envelope (n : Nat) :
    diagonalOperatorTower14Family n ≤ incoming14Envelope n :=
  Nat.le_trans (BigNumber.le_maxN_left _ _)
    (BigNumber.le_maxN_right _ _)

theorem rdor14Family_le_envelope (n : Nat) :
    rdor14Family n ≤ incoming14Envelope n :=
  Nat.le_trans
    (Nat.le_trans (BigNumber.le_maxN_left _ _)
      (BigNumber.le_maxN_right _ _))
    (BigNumber.le_maxN_right _ _)

theorem rankDiagonal14Family_le_envelope (n : Nat) :
    rankDiagonal14Family n ≤ incoming14Envelope n :=
  Nat.le_trans
    (Nat.le_trans (BigNumber.le_maxN_right _ _)
      (BigNumber.le_maxN_right _ _))
    (BigNumber.le_maxN_right _ _)

theorem incoming14Envelope_lt_family14 (n : Nat) :
    incoming14Envelope n < family14 n := by
  unfold family14
  omega

theorem input_lt_family14 (n : Nat) : n < family14 n := by
  unfold family14
  omega

theorem diagonalHyper14Family_lt_family14 (n : Nat) :
    diagonalHyper14Family n < family14 n :=
  Nat.lt_of_le_of_lt (diagonalHyper14Family_le_envelope n)
    (incoming14Envelope_lt_family14 n)

theorem diagonalOperatorTower14Family_lt_family14 (n : Nat) :
    diagonalOperatorTower14Family n < family14 n :=
  Nat.lt_of_le_of_lt (diagonalOperatorTower14Family_le_envelope n)
    (incoming14Envelope_lt_family14 n)

theorem rdor14Family_lt_family14 (n : Nat) :
    rdor14Family n < family14 n :=
  Nat.lt_of_le_of_lt (rdor14Family_le_envelope n)
    (incoming14Envelope_lt_family14 n)

theorem rankDiagonal14Family_lt_family14 (n : Nat) :
    rankDiagonal14Family n < family14 n :=
  Nat.lt_of_le_of_lt (rankDiagonal14Family_le_envelope n)
    (incoming14Envelope_lt_family14 n)

/-! ## Diagonal base and outer metatower -/

theorem diagonalTransformer15_progressive :
    Progressive diagonalTransformer15 := by
  intro seed i o n hi
  have h :=
    ((diagonalLift_preservesProgressive (schedule15 n) (rank15 n))
      fdFamilyTransformer fdFamilyTransformer_progressive)
      seed i o n hi
  simpa [diagonalTransformer15] using h

theorem fdFamilyTransformer_lt_diagonalTransformer15
    (seed : W.Family) {i o n : Nat} (hi : i ≤ n) :
    fdFamilyTransformer seed i n < diagonalTransformer15 seed o n := by
  have h :=
    (diagonalLift_strictlyInflationary (schedule15 n) (rank15 n))
      fdFamilyTransformer fdFamilyTransformer_progressive seed i o n hi
  simpa [diagonalTransformer15] using h

theorem metaTower15_progressive : ∀ k, Progressive (metaTower15 k)
  | 0 => diagonalTransformer15_progressive
  | k + 1 => by
      simpa [metaTower15, metaStep15] using
        (operatorStage_progressive (metaTower15 k)
          (metaTower15_progressive k) tree15)

theorem transformer_lt_metaStep15 {op : Transformer}
    (hop : Progressive op) (seed : W.Family) {i o n : Nat} (hi : i ≤ n) :
    op seed i n < metaStep15 op seed o n := by
  have hLift : op seed i n < liftTransformer op seed 0 n :=
    transformer_lt_lift_at hop seed hi
  have hLeaf : op seed i n < operatorStage op (.leaf) seed 0 n := by
    simpa [operatorStage] using hLift
  have hCrownRaw :=
    operatorStage_child_lt op hop seed (crown15 coreTree15)
      (i := 0) (o := o) (n := n) (Nat.zero_le n)
  have hCrown :
      operatorStage op (.leaf) seed 0 n <
        operatorStage op tree15 seed o n := by
    simpa [tree15, crown15] using hCrownRaw
  exact Nat.lt_trans hLeaf (by simpa [metaStep15] using hCrown)

theorem coreStage_lt_crowned15 {op : Transformer}
    (hop : Progressive op) (core : BigNumber.WTree Nat) (seed : W.Family)
    {o n : Nat} (h1 : 1 ≤ n) :
    operatorStage op core seed 0 n <
      operatorStage op (.node (crown15 core)) seed o n := by
  have hCore :=
    operatorStage_child_lt op hop seed (crown15 core)
      (i := 1) (o := o) (n := n) h1
  simpa [crown15] using hCore

theorem metaTower15_step_lt (k : Nat) (seed : W.Family)
    {i o n : Nat} (hi : i ≤ n) :
    metaTower15 k seed i n < metaTower15 (k + 1) seed o n := by
  simpa [metaTower15] using
    (transformer_lt_metaStep15 (metaTower15_progressive k) seed hi)

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

theorem family14_lt_F15 (n : Nat) : family14 n < F15 n := by
  have h :=
    metaTower15_progressive (ramification15 n + 1)
      seed14 0 n n (Nat.zero_le n)
  simpa [F15, seed14] using h

theorem diagonalTransformer15_lt_F15 (n : Nat) :
    diagonalTransformer15 seed14 n n < F15 n := by
  have h :=
    diagonalTransformer15_lt_metaTower15_succ (ramification15 n) seed14
      (i := n) (o := n) (n := n) (Nat.le_refl n)
  simpa [F15] using h

theorem reflectFdFamily_lt_diagonalTransformer15 (n : Nat) :
    reflectFdFamily seed14 n < diagonalTransformer15 seed14 n n := by
  have h :=
    fdFamilyTransformer_lt_diagonalTransformer15 seed14
      (i := n) (o := n) (n := n) (Nat.le_refl n)
  simpa [fdFamilyTransformer] using h

theorem fvalue_lt_F15 {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily seed14) n t < F15 n :=
  Nat.lt_trans (fvalue_lt_reflectFdFamily seed14 ht)
    (Nat.lt_trans (reflectFdFamily_lt_diagonalTransformer15 n)
      (diagonalTransformer15_lt_F15 n))

theorem input_lt_F15 (n : Nat) : n < F15 n :=
  Nat.lt_trans (input_lt_family14 n) (family14_lt_F15 n)

/-! ## Closed comparisons with every current incoming candidate -/

theorem family14_42_lt_contender_15 : family14 42 < contender_15 :=
  Nat.lt_trans (family14_lt_F15 42) (input_lt_F15 (F15 42))

theorem contender_14_lt_contender_15 : contender_14 < contender_15 :=
  Nat.lt_trans (diagonalHyper14Family_lt_family14 42)
    family14_42_lt_contender_15

theorem diagonalOperatorTower14_lt_contender_15 :
    Incoming14.DiagonalOperatorTower.contender_14 < contender_15 :=
  Nat.lt_trans (diagonalOperatorTower14Family_lt_family14 42)
    family14_42_lt_contender_15

theorem rdor14_lt_contender_15 :
    Incoming14.RDOR.contender_14 < contender_15 :=
  Nat.lt_trans (rdor14Family_lt_family14 42)
    family14_42_lt_contender_15

theorem rankDiagonal14_lt_contender_15 :
    Incoming14.RankDiagonal.contender_14 < contender_15 :=
  Nat.lt_trans (rankDiagonal14Family_lt_family14 42)
    family14_42_lt_contender_15

theorem contender_13_lt_contender_15 : contender_13 < contender_15 :=
  Nat.lt_trans contender_13_lt_contender_14 contender_14_lt_contender_15

theorem fvalue_lt_contender_15 {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo (F15 42)) :
    Fd.fvalue (packFamily seed14) (F15 42) t < contender_15 :=
  fvalue_lt_F15 ht

end BusyLean
