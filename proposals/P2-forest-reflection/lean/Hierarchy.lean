import Original
import Trees

/-!
Tree-indexed iteration of a constructive reflection operator.
This file uses raw well-founded trees, not a quotient by ordinal equality.
-/

namespace Hierarchy

abbrev Unary := Nat → Nat
abbrev Transformer := Unary → Unary

/-- The maximum of the first `k + 1` values, including index zero. -/
def prefixMax (f : Unary) : Nat → Nat
  | 0 => f 0
  | k + 1 => Nat.max (prefixMax f k) (f (k + 1))

theorem le_prefixMax (f : Unary) (k i : Nat) (h : i ≤ k) :
    f i ≤ prefixMax f k := by
  induction k with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero h
      rw [hi]
      exact Nat.le_refl (f 0)
  | succ k ih =>
      cases Nat.eq_or_lt_of_le h with
      | inl heq =>
          rw [heq]
          exact Original.le_natMax_right (prefixMax f k) (f (k + 1))
      | inr hlt =>
          exact Nat.le_trans (ih (Nat.le_of_lt_succ hlt))
            (Original.le_natMax_left (prefixMax f k) (f (k + 1)))

/-- Successors reflect their predecessor; limits reflect a finite join. -/
def stage (R : Transformer) : BTree → Unary
  | .zero => R Nat.succ
  | .succ a => R (stage R a)
  | .lim children =>
      R (fun n => prefixMax (fun i => stage R (children i) n) n)
termination_by structural a => a

theorem stage_succ_gt (R : Transformer)
    (hR : ∀ f n, f n < R f n) (a : BTree) (n : Nat) :
    stage R a n < stage R (.succ a) n := hR (stage R a) n

theorem stage_child_lt_limit (R : Transformer)
    (hR : ∀ f n, f n < R f n)
    (children : Nat → BTree) (n i : Nat) (hi : i ≤ n) :
    stage R (children i) n < stage R (.lim children) n :=
  Nat.lt_of_le_of_lt (le_prefixMax (fun j => stage R (children j) n) n i hi)
    (hR (fun m => prefixMax (fun j => stage R (children j) m) m) n)

/-- Transfer a reflector lower bound at one chosen numerical argument. -/
theorem lower_bound_at (R : Transformer) (bound n : Nat)
    (hR : ∀ f, bound < R f n) (a : BTree) : bound < stage R a n := by
  cases a with
  | zero => exact hR Nat.succ
  | succ a => exact hR (stage R a)
  | lim children =>
      exact hR (fun m => prefixMax (fun i => stage R (children i) m) m)

/-- Every node has the same uniform lower bound as the reflector itself. -/
theorem uniform_lower_bound (R : Transformer) (bound : Unary)
    (hR : ∀ f n, bound n < R f n) (a : BTree) (n : Nat) :
    bound n < stage R a n := by
  cases a with
  | zero => exact hR Nat.succ n
  | succ a => exact hR (stage R a) n
  | lim children =>
      exact hR (fun m => prefixMax (fun i => stage R (children i) m) m) n

/-- Add a visible spine of `k` successor reflection steps. -/
def pad (a : BTree) : Nat → BTree
  | 0 => a
  | k + 1 => .succ (pad a k)

/-- Iterate a reflector at the function level, without evaluating any value. -/
def reflectIter (R : Transformer) : Nat → Unary → Unary
  | 0, f => f
  | k + 1, f => R (reflectIter R k f)

/-- Padding is literally iteration of the reflection operator. -/
theorem pad_stage_eq_reflectIter (R : Transformer) (a : BTree) (k : Nat) :
    stage R (pad a k) = reflectIter R k (stage R a) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg R ih

/-- The pointwise version needs no function extensionality. -/
theorem pad_stage_apply (R : Transformer) (a : BTree) (k n : Nat) :
    stage R (pad a k) n = reflectIter R k (stage R a) n :=
  congrFun (pad_stage_eq_reflectIter R a k) n

/-- A diagonal limit of all positive finite successor spines. -/
def diagonalTree (a : BTree) : BTree := .lim (fun k => pad a (k + 1))

/-- The value at `n` dominates each of the first `n + 1` reflection heights. -/
theorem reflectIter_lt_diagonal (R : Transformer)
    (hR : ∀ f n, f n < R f n) (a : BTree) (n i : Nat) (hi : i ≤ n) :
    reflectIter R (i + 1) (stage R a) n < stage R (diagonalTree a) n := by
  have h := stage_child_lt_limit R hR (fun k => pad a (k + 1)) n i hi
  rw [pad_stage_apply] at h
  exact h

/-- The generic hierarchy depends on tree presentation, even at rank zero. -/
theorem zero_lt_constant_zero_limit (R : Transformer)
    (hR : ∀ f n, f n < R f n) (n : Nat) :
    stage R .zero n < stage R (.lim (fun _ => .zero)) n :=
  stage_child_lt_limit R hR (fun _ => .zero) n 0 (Nat.zero_le n)

theorem pad_growth (R : Transformer)
    (hR : ∀ f n, f n < R f n) (a : BTree) (n k : Nat) :
    stage R a n + k ≤ stage R (pad a k) n := by
  induction k with
  | zero => exact Nat.le_refl (stage R a n)
  | succ k ih =>
      exact Nat.le_trans (Nat.succ_le_succ ih)
        (stage_succ_gt R hR (pad a k) n)

theorem reflectIter_mono (R : Transformer)
    (hR : ∀ f n, f n < R f n) (f : Unary) (n i j : Nat) (h : i ≤ j) :
    reflectIter R i f n ≤ reflectIter R j f n := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step j hj ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (hR (reflectIter R j f) n))

/-- Every fixed finite reflection height is eventually below the diagonal. -/
theorem fixed_reflection_lt_diagonal (R : Transformer)
    (hR : ∀ f n, f n < R f n) (a : BTree) (n k : Nat) (hk : k ≤ n + 1) :
    reflectIter R k (stage R a) n < stage R (diagonalTree a) n :=
  Nat.lt_of_le_of_lt (reflectIter_mono R hR (stage R a) n k (n + 1) hk)
    (reflectIter_lt_diagonal R hR a n n (Nat.le_refl n))

/-- A direct additive consequence of the visible successor spine. -/
theorem diagonal_gap (R : Transformer)
    (hR : ∀ f n, f n < R f n) (a : BTree) (n : Nat) :
    stage R a n + (n + 2) ≤ stage R (diagonalTree a) n := by
  have hp := pad_growth R hR a n (n + 1)
  have hlt := stage_child_lt_limit R hR (fun k => pad a (k + 1)) n n
    (Nat.le_refl n)
  exact Nat.le_trans (Nat.succ_le_succ hp) hlt

/-- Transport the small gap index before specializing a huge closed value. -/
theorem diagonal_gap_at (R : Transformer)
    (hR : ∀ f n, f n < R f n) (a : BTree) (n k : Nat) (hk : n + 2 = k) :
    stage R a n + k ≤ stage R (diagonalTree a) n := by
  cases hk
  exact diagonal_gap R hR a n

theorem lower_bound_diagonal_gap (R : Transformer)
    (hR : ∀ f n, f n < R f n) (a : BTree) (n bound : Nat)
    (hb : bound < stage R a n) :
    bound + (n + 3) ≤ stage R (diagonalTree a) n :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_right hb (n + 2)) (diagonal_gap R hR a n)

theorem lower_bound_diagonal_gap_at (R : Transformer)
    (hR : ∀ f n, f n < R f n) (a : BTree) (n bound k : Nat)
    (hb : bound < stage R a n) (hk : n + 3 = k) :
    bound + k ≤ stage R (diagonalTree a) n := by
  cases hk
  exact lower_bound_diagonal_gap R hR a n bound hb

/-- A one-step tree descent whose chosen limit index is bounded by `n`. -/
inductive Step (n : Nat) : BTree → BTree → Prop where
  | succ (a : BTree) : Step n a (.succ a)
  | limit (children : Nat → BTree) (i : Nat) (hi : i ≤ n) :
      Step n (children i) (.lim children)

theorem step_growth (R : Transformer) (hR : ∀ f n, f n < R f n)
    {n : Nat} {a b : BTree} (h : Step n a b) :
    stage R a n < stage R b n := by
  cases h with
  | succ a => exact stage_succ_gt R hR a n
  | limit children i hi => exact stage_child_lt_limit R hR children n i hi

/-- A finite path is explicit evidence of the accumulated strict gap. -/
inductive Path (n : Nat) : BTree → BTree → Nat → Prop where
  | refl (a : BTree) : Path n a a 0
  | extend {a b c : BTree} {k : Nat} :
      Path n a b k → Step n b c → Path n a c (k + 1)

theorem path_growth (R : Transformer) (hR : ∀ f n, f n < R f n)
    {n : Nat} {a b : BTree} {k : Nat} (h : Path n a b k) :
    stage R a n + k ≤ stage R b n := by
  induction h with
  | refl => exact Nat.le_refl (stage R a n)
  | extend path edge ih =>
      exact Nat.le_trans (Nat.succ_le_succ ih) (step_growth R hR edge)

end Hierarchy
