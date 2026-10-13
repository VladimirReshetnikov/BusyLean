import BusyLean.Contender14
import BusyLean.Comparison13
import BusyLean.MetaReflectionFacts

/-! # Contender 14: comparison and structural-margin theorems -/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-! ## The family-aware dynamic-kind reflection step -/

/-- Anything bounded by the explicit maximum is strictly below `reflect14`. -/
theorem lt_reflect14 {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN
      (W.prefixMax (fun i => fs i n) n)
      (Fd.reflectFd (packFamily fs) n)) :
    m < reflect14 fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every family coordinate visible at the current input is strictly below the
new reflection step. -/
theorem oracle_lt_reflect14 (fs : W.Family) {i n : Nat}
    (hi : i ≤ n) : fs i n < reflect14 fs n :=
  lt_reflect14
    (Nat.le_trans
      (W.le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- The underlying unary dynamic-kind reflection is itself strictly below the
family-aware reflection step. -/
theorem packed_reflection_lt_reflect14 (fs : W.Family) (n : Nat) :
    Fd.reflectFd (packFamily fs) n < reflect14 fs n :=
  lt_reflect14 (BigNumber.le_maxN_right _ _)

/-- Every accepted dynamic-kind program at the current budget is strictly
below the family-aware reflection step. -/
theorem fvalue_lt_reflect14 (fs : W.Family) {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily fs) n t < reflect14 fs n :=
  Nat.lt_trans
    (Fd.fvalue_lt_reflectFd (packFamily fs) ht)
    (packed_reflection_lt_reflect14 fs n)

/-- The numerical input is strictly below every family-aware reflection step. -/
theorem input_lt_reflect14 (fs : W.Family) (n : Nat) :
    n < reflect14 fs n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

/-- The base dynamic-kind transformer is progressive. -/
theorem fdTransformer_progressive : Progressive fdTransformer := by
  intro seed i o n hi
  exact oracle_lt_reflect14 seed hi

/-! ## Generic operator-power lemmas -/

/-- Progressivity is preserved by every finite operator power. -/
theorem operatorPower_progressive (tree : WTree Nat)
    {base : Transformer} (hbase : Progressive base) :
    ∀ k, Progressive (operatorPower tree base k)
  | 0 => hbase
  | k + 1 =>
      operatorStage_progressive
        (operatorPower tree base k)
        (operatorPower_progressive tree hbase k)
        tree

/-- A progressive transformer is strictly below one complete operator stage,
at every visible input coordinate.  The proof follows coordinate zero through
one child at every node; no monotonicity in the oracle is assumed. -/
theorem transformer_lt_operatorStage (base : Transformer)
    (hbase : Progressive base) (seed : Family) :
    ∀ (a : WTree Nat) (i o n : Nat), i ≤ n →
      base seed i n < operatorStage base a seed o n
  | .leaf, i, o, n, hi =>
      transformer_lt_lift_at (op := base) hbase seed
        (i := i) (o := o) (n := n) hi
  | .node f, i, o, n, hi =>
      Nat.lt_trans
        (transformer_lt_operatorStage base hbase seed
          (f 0) i 0 n hi)
        (operatorStage_child_lt base hbase seed f
          (i := 0) (o := o) (n := n) (Nat.zero_le n))

/-- Consecutive operator powers form a strict chain. -/
theorem operatorPower_step_lt (tree : WTree Nat)
    (base : Transformer) (hbase : Progressive base) (seed : Family)
    (k i o n : Nat) (hi : i ≤ n) :
    operatorPower tree base k seed i n <
      operatorPower tree base (k + 1) seed o n :=
  transformer_lt_operatorStage
    (operatorPower tree base k)
    (operatorPower_progressive tree hbase k)
    seed tree i o n hi

/-- Every positive operator power strictly exceeds the original base
transformer. -/
theorem transformer_lt_operatorPower (tree : WTree Nat)
    (base : Transformer) (hbase : Progressive base) (seed : Family) :
    ∀ (k i o n : Nat), i ≤ n →
      base seed i n < operatorPower tree base (k + 1) seed o n
  | 0, i, o, n, hi =>
      transformer_lt_operatorStage base hbase seed tree i o n hi
  | k + 1, i, o, n, hi =>
      Nat.lt_trans
        (transformer_lt_operatorPower tree base hbase seed
          k i 0 n hi)
        (transformer_lt_operatorStage
          (operatorPower tree base (k + 1))
          (operatorPower_progressive tree hbase (k + 1))
          seed tree 0 o n (Nat.zero_le n))

/-! ## The diagonal family and the required comparison -/

/-- Contender 13's family strictly exceeds its input. -/
theorem input_lt_family13 (n : Nat) : n < family13 n :=
  Nat.lt_trans
    (Fd.input_lt_reflectFd family12 n)
    (Fd.input_lt_reflectFd family12 (F13 n))

/-- The previous family, evaluated once more at its own value, is still below
`F14`.  This is the direct progressivity margin of the final transformer. -/
theorem family13_twice_lt_F14 (n : Nat) :
    family13 (family13 n) < F14 n := by
  change family13 (family13 n) <
    operatorPower tree14 fdTransformer (family13 n + 1)
      (fun _ => family13) (family13 n) (family13 n)
  exact
    (operatorPower_progressive tree14 fdTransformer_progressive
      (family13 n + 1))
      (fun _ => family13) 0 (family13 n) (family13 n)
      (Nat.zero_le (family13 n))

/-- The base family-aware reflection step at the diagonal budget lies below the
whole positive operator power. -/
theorem reflect14_lt_F14 (n : Nat) :
    reflect14 (fun _ => family13) (family13 n) < F14 n := by
  change fdTransformer (fun _ => family13) 0 (family13 n) <
    operatorPower tree14 fdTransformer (family13 n + 1)
      (fun _ => family13) (family13 n) (family13 n)
  exact transformer_lt_operatorPower
    tree14 fdTransformer fdTransformer_progressive
    (fun _ => family13) (family13 n) 0
    (family13 n) (family13 n) (Nat.zero_le (family13 n))

/-- At every input, `F14` strictly exceeds Contender 13's complete family. -/
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n :=
  Nat.lt_trans
    (input_lt_family13 (family13 n))
    (family13_twice_lt_F14 n)

/-- The final diagonal strictly exceeds its own numerical input. -/
theorem input_lt_F14 (n : Nat) : n < F14 n :=
  Nat.lt_trans (input_lt_family13 n) (family13_lt_F14 n)

/-- Every accepted dynamic-kind program at the diagonal budget, using the
packed constant family `family13`, is below `F14 n`. -/
theorem fvalue_lt_F14 {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo (family13 n)) :
    Fd.fvalue (packFamily (fun _ => family13)) (family13 n) t < F14 n :=
  Nat.lt_trans
    (fvalue_lt_reflect14 (fun _ => family13) ht)
    (reflect14_lt_F14 n)

/-- **The required comparison:** Contender 13 is strictly smaller than
Contender 14. -/
theorem contender_13_lt_contender_14 : contender_13 < contender_14 := by
  change family13 42 < F14 (F14 42)
  exact Nat.lt_trans (family13_lt_F14 42) (input_lt_F14 (F14 42))

/-- All earlier accepted contenders are therefore also below Contender 14. -/
theorem contender_12_lt_contender_14 : contender_12 < contender_14 :=
  Nat.lt_trans contender_12_lt_contender_13 contender_13_lt_contender_14

end BusyLean
