import BusyLean.Contender14
import BusyLean.MetaReflectionFacts
import BusyLean.Comparison13

/-! # Contender 14: comparison theorems -/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- The arithmetic core of family-aware dynamic-kind reflection. -/
theorem lt_reflect14 {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fd.fvalue (packFamily fs) n) (Fd.ctmsUpTo n))) :
    m < reflect14 fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible coordinate of the oracle family is strictly exceeded. -/
theorem oracle_lt_reflect14 (fs : W.Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflect14 fs n :=
  lt_reflect14
    (Nat.le_trans (W.le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every enumerated dynamic-kind program, run with the packed family oracle,
is strictly exceeded by one reflection step. -/
theorem fvalue_lt_reflect14 (fs : W.Family) {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily fs) n t < reflect14 fs n :=
  lt_reflect14
    (Nat.le_trans (W.le_maximum (Fd.fvalue (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- The numerical input is strictly exceeded by one reflection step. -/
theorem input_lt_reflect14 (fs : W.Family) (n : Nat) : n < reflect14 fs n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

/-- Family-aware dynamic-kind reflection is a progressive transformer. -/
theorem fdFamilyTransformer_progressive : Progressive fdFamilyTransformer := by
  intro seed i o n hi
  exact oracle_lt_reflect14 seed hi

/-- Every finite rank of the diagonal operator tower is progressive. -/
theorem diagonalOperatorTower_progressive
    (schedule : Nat → WTree Nat) (base : Transformer)
    (hbase : Progressive base) (k : Nat) :
    Progressive (diagonalOperatorTower schedule base k) := by
  induction k with
  | zero => simpa [diagonalOperatorTower] using hbase
  | succ k ih =>
      simpa [diagonalOperatorTower] using
        (operatorStage_progressive
          (diagonalOperatorTower schedule base k) ih (schedule k))

/-- One use of `schedule14 k` strictly raises every visible value of a
progressive transformer.  The proof uses only the explicit leaf at branch zero;
it does not assume any monotonicity of reflection in an oracle. -/
theorem transformer_lt_operatorStage_schedule14 {base : Transformer}
    (hbase : Progressive base) (seed : W.Family) (k : Nat)
    {i o n : Nat} (hi : i ≤ n) :
    base seed i n < operatorStage base (schedule14 k) seed o n := by
  let f : Nat → WTree Nat := fun j =>
    match j with
    | 0 => .leaf
    | r + 1 =>
        Autonomous.realize
          (Autonomous.hyper (k + r + 1) (Autonomous.encode tree12))
  have h1 : base seed i n < liftTransformer base seed 0 n :=
    transformer_lt_lift_at hbase seed hi
  have h2 : operatorStage base (f 0) seed 0 n <
      operatorStage base (.node f) seed o n :=
    operatorStage_child_lt base hbase seed f (Nat.zero_le n)
  have h2' : liftTransformer base seed 0 n <
      operatorStage base (schedule14 k) seed o n := by
    simpa [f, schedule14] using h2
  exact Nat.lt_trans h1 h2'

/-- Consecutive ranks of the concrete tower are pointwise strictly increasing
at every visible coordinate. -/
theorem diagonalOperatorTower_step_lt (seed : W.Family) (k : Nat)
    {i o n : Nat} (hi : i ≤ n) :
    diagonalOperatorTower schedule14 fdFamilyTransformer k seed i n <
      diagonalOperatorTower schedule14 fdFamilyTransformer (k + 1) seed o n := by
  simpa [diagonalOperatorTower] using
    (transformer_lt_operatorStage_schedule14
      (diagonalOperatorTower_progressive schedule14 fdFamilyTransformer
        fdFamilyTransformer_progressive k)
      seed k hi)

/-- Every lower rank is pointwise strictly below every higher rank at visible
coordinates.  This is the finite transitive closure of the one-step theorem. -/
theorem diagonalOperatorTower_rank_lt (seed : W.Family)
    {k l i o n : Nat} (hi : i ≤ n) (hkl : k < l) :
    diagonalOperatorTower schedule14 fdFamilyTransformer k seed i n <
      diagonalOperatorTower schedule14 fdFamilyTransformer l seed o n := by
  induction l generalizing k i o with
  | zero =>
      exact False.elim (Nat.not_lt_zero k hkl)
  | succ l ih =>
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hkl) with
      | inl hlt =>
          exact Nat.lt_trans
            (ih (k := k) (i := i) (o := 0) hi hlt)
            (diagonalOperatorTower_step_lt seed l (i := 0)
              (o := o) (n := n) (Nat.zero_le n))
      | inr heq =>
          subst k
          exact diagonalOperatorTower_step_lt seed l hi

/-- At every input, `F14` strictly exceeds Contender 13's entire family. -/
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n := by
  change family13 n <
    diagonalOperatorTower schedule14 fdFamilyTransformer (family13 n)
      (fun _ => family13) n n
  exact
    (diagonalOperatorTower_progressive schedule14 fdFamilyTransformer
      fdFamilyTransformer_progressive (family13 n))
      (fun _ => family13) 0 n n (Nat.zero_le n)

/-- `F13` is input-increasing. -/
theorem input_lt_F13 (n : Nat) : n < F13 n :=
  Fd.input_lt_reflectFd family12 n

/-- The family used as the rank and seed of Contender 14 is input-increasing. -/
theorem input_lt_family13 (n : Nat) : n < family13 n :=
  Nat.lt_trans (input_lt_F13 n) (input_lt_F13 (F13 n))

/-- `F14` is input-increasing. -/
theorem input_lt_F14 (n : Nat) : n < F14 n :=
  Nat.lt_trans (input_lt_family13 n) (family13_lt_F14 n)

/-- The self-indexing rank is positive at every input. -/
theorem zero_lt_family13 (n : Nat) : 0 < family13 n :=
  Nat.lt_of_le_of_lt (Nat.zero_le n) (input_lt_family13 n)

/-- Every proper lower tower rank is below the selected self-indexed rank. -/
theorem lower_rank_lt_F14 {k n : Nat} (hk : k < family13 n) :
    diagonalOperatorTower schedule14 fdFamilyTransformer k
        (fun _ => family13) 0 n < F14 n := by
  change diagonalOperatorTower schedule14 fdFamilyTransformer k
      (fun _ => family13) 0 n <
    diagonalOperatorTower schedule14 fdFamilyTransformer (family13 n)
      (fun _ => family13) n n
  exact diagonalOperatorTower_rank_lt (fun _ => family13)
    (i := 0) (o := n) (n := n) (Nat.zero_le n) hk

/-- Even the rank-zero family-aware dynamic reflector is below `F14`. -/
theorem reflect14_seed_lt_F14 (n : Nat) :
    reflect14 (fun _ => family13) n < F14 n := by
  simpa [diagonalOperatorTower, fdFamilyTransformer] using
    (lower_rank_lt_F14 (k := 0) (n := n) (zero_lt_family13 n))

/-- Every dynamic-kind program enumerated at depth `n`, run with the packed
Contender-13 family oracle, is strictly below `F14 n`. -/
theorem fvalue_lt_F14 {n : Nat} {t : Fd.CTm} (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily (fun _ => family13)) n t < F14 n :=
  Nat.lt_trans (fvalue_lt_reflect14 (fun _ => family13) ht)
    (reflect14_seed_lt_F14 n)

/-- The tower rank at input 42 is definitionally the previous contender. -/
theorem tower14_rank_at_42 :
    tower14 42 =
      diagonalOperatorTower schedule14 fdFamilyTransformer contender_13 := by
  rfl

/-- **The required comparison:** Contender 13 is strictly smaller than
Contender 14. -/
theorem contender_13_lt_contender_14 : contender_13 < contender_14 := by
  simpa [contender_13, contender_14, family13] using
    (Nat.lt_trans (family13_lt_F14 42) (input_lt_F14 (F14 42)))

/-- All previously accepted contenders are therefore smaller as well. -/
theorem contender_12_lt_contender_14 : contender_12 < contender_14 :=
  Nat.lt_trans contender_12_lt_contender_13 contender_13_lt_contender_14

end BusyLean
