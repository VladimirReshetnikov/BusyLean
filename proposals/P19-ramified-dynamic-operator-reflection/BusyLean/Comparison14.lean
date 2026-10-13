import BusyLean.Contender14
import BusyLean.Comparison13
import BusyLean.MetaReflectionFacts

/-!
# Contender 14: comparison and lower-bound theorems

The main result is `contender_13_lt_contender_14`.  The proof does not evaluate
any contender.  It factors through generic progressivity of operator stages.

A stronger quantitative certificate is also exposed: at every input `n`,
`F14 n` dominates every visible seed coordinate.  In particular, `F14 42`
dominates forty-two further iterations of `F13` starting at `contender_13`,
before the final outer application of `F14` is taken.
-/

namespace BusyLean

/-! ## Family-aware dynamic-kind reflection -/

/-- Anything below the maximum component is strictly below the reflector. -/
theorem lt_reflectFdFamily {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN
      (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fd.fvalue (packFamily fs) n) (Fd.ctmsUpTo n))) :
    m < reflectFdFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible oracle-family coordinate is strictly below the reflector. -/
theorem oracle_lt_reflectFdFamily (fs : W.Family) {i n : Nat}
    (hi : i ≤ n) : fs i n < reflectFdFamily fs n :=
  lt_reflectFdFamily
    (Nat.le_trans (W.le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every accepted dynamic-kind program in the bounded enumeration is strictly
below the reflector, with access to the packed family oracle. -/
theorem fvalue_lt_reflectFdFamily (fs : W.Family) {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily fs) n t < reflectFdFamily fs n :=
  lt_reflectFdFamily
    (Nat.le_trans (W.le_maximum _ ht) (BigNumber.le_maxN_right _ _))

/-- The numerical input is strictly below family-aware reflection. -/
theorem input_lt_reflectFdFamily (fs : W.Family) (n : Nat) :
    n < reflectFdFamily fs n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

/-- Family-aware dynamic-kind reflection is a progressive transformer. -/
theorem fdFamilyTransformer_progressive :
    Progressive fdFamilyTransformer := by
  intro seed i o n hi
  exact oracle_lt_reflectFdFamily seed hi

/-! ## A strict tower of operator closures -/

/-- One tower step strictly dominates its base transformer at every visible
coordinate. -/
theorem transformer_lt_towerStep {base : Transformer}
    (hbase : Progressive base) (seed : W.Family)
    {i o n : Nat} (hi : i ≤ n) :
    base seed i n < towerStep base seed o n := by
  change base seed i n < operatorStage base tree14 (base seed) o n
  exact (operatorStage_progressive base hbase tree14)
    (base seed) i o n hi

/-- A tower step over a progressive transformer remains progressive. -/
theorem towerStep_progressive {base : Transformer}
    (hbase : Progressive base) : Progressive (towerStep base) := by
  intro seed i o n hi
  exact Nat.lt_trans
    (hbase seed i i n hi)
    (transformer_lt_towerStep hbase seed
      (i := i) (o := o) (n := n) hi)

/-- Every level of the ramified operator tower is progressive. -/
theorem operatorTower_progressive :
    (k : Nat) → Progressive (operatorTower k)
  | 0 => fdFamilyTransformer_progressive
  | k + 1 => towerStep_progressive (operatorTower_progressive k)

/-- Successive tower levels form a strict pointwise chain on visible
coordinates. -/
theorem operatorTower_level_lt_succ (k : Nat) (seed : W.Family)
    {i o n : Nat} (hi : i ≤ n) :
    operatorTower k seed i n < operatorTower (k + 1) seed o n := by
  change operatorTower k seed i n <
    towerStep (operatorTower k) seed o n
  exact transformer_lt_towerStep (operatorTower_progressive k) seed hi

/-- The base dynamic-family reflector is below every positive tower level. -/
theorem fdFamilyTransformer_lt_operatorTower_succ :
    ∀ (k : Nat) (seed : W.Family) (o n : Nat),
      fdFamilyTransformer seed 0 n <
        operatorTower (k + 1) seed o n
  | 0, seed, o, n =>
      operatorTower_level_lt_succ 0 seed
        (i := 0) (o := o) (n := n) (Nat.zero_le n)
  | k + 1, seed, o, n =>
      Nat.lt_trans
        (fdFamilyTransformer_lt_operatorTower_succ k seed 0 n)
        (operatorTower_level_lt_succ (k + 1) seed
          (i := 0) (o := o) (n := n) (Nat.zero_le n))

/-! ## The seed and the final comparison -/

@[simp] theorem seed13_zero (n : Nat) : seed13 0 n = family13 n := rfl

/-- Every application of `F13` is strictly input-increasing. -/
theorem input_lt_F13 (n : Nat) : n < F13 n :=
  Fd.input_lt_reflectFd family12 n

/-- Any nonempty finite iteration of `F13` strictly exceeds its starting
value.  No monotonicity assumption on `F13` is needed. -/
theorem input_lt_iterateF13_succ :
    ∀ (k n : Nat), n < iterateF13 (k + 1) n
  | 0, n => input_lt_F13 n
  | k + 1, n =>
      Nat.lt_trans
        (input_lt_iterateF13_succ k n)
        (input_lt_F13 (iterateF13 (k + 1) n))

/-- Every seed coordinate visible at input `n` is below `F14 n`. -/
theorem seed13_lt_F14 {i n : Nat} (hi : i ≤ n) :
    seed13 i n < F14 n :=
  operatorTower_progressive (n + 1) seed13 i n n hi

/-- At every input, `F14` exceeds the whole Contender-13 family. -/
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n := by
  rw [← seed13_zero n]
  exact seed13_lt_F14 (i := 0) (n := n) (Nat.zero_le n)

/-- The exact formal margin at the contest input: `F14 42` already exceeds
forty-two additional `F13` iterations starting from Contender 13. -/
theorem fortyTwo_F13_steps_lt_F14 :
    iterateF13 42 contender_13 < F14 42 := by
  change seed13 42 42 < F14 42
  exact seed13_lt_F14 (i := 42) (n := 42) (Nat.le_refl 42)

/-- The Contender-13 family itself is input-increasing. -/
theorem input_lt_family13 (n : Nat) : n < family13 n :=
  Nat.lt_trans (input_lt_F13 n) (input_lt_F13 (F13 n))

/-- `F14` is input-increasing. -/
theorem input_lt_F14 (n : Nat) : n < F14 n :=
  Nat.lt_trans (input_lt_family13 n) (family13_lt_F14 n)

/-- **The required comparison:** Contender 13 is strictly smaller than
Contender 14. -/
theorem contender_13_lt_contender_14 : contender_13 < contender_14 :=
  Nat.lt_trans (family13_lt_F14 42) (input_lt_F14 (F14 42))

/-- Consequently, Contender 12 is also below Contender 14. -/
theorem contender_12_lt_contender_14 : contender_12 < contender_14 :=
  Nat.lt_trans contender_12_lt_contender_13 contender_13_lt_contender_14

/-- Every bounded dynamic-kind program using the packed, iterated
Contender-13 seed family is below `F14` at the same input. -/
theorem fvalue_lt_F14 {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily seed13) n t < F14 n := by
  have h₁ : Fd.fvalue (packFamily seed13) n t <
      fdFamilyTransformer seed13 0 n :=
    fvalue_lt_reflectFdFamily seed13 ht
  have h₂ : fdFamilyTransformer seed13 0 n < F14 n :=
    fdFamilyTransformer_lt_operatorTower_succ n seed13 n n
  exact Nat.lt_trans h₁ h₂

/-- The same program-domination result at Contender 14's outer budget. -/
theorem fvalue_lt_contender_14 {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo (F14 42)) :
    Fd.fvalue (packFamily seed13) (F14 42) t < contender_14 :=
  fvalue_lt_F14 ht

end BusyLean
