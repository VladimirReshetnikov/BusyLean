import Forest

/-!
A tree hierarchy whose limit stage preserves access to its entire child
family. Comparisons use the explicit child index and never assume that a
reflection operator is monotone in the numerical values of its oracles.
-/

namespace ForestHierarchy

/-- One successor-level reflection, with a constant indexed oracle family. -/
def step (f : Nat → Nat) : Nat → Nat := Forest.reflect (fun _ => f)

theorem self_lt_step (f : Nat → Nat) (n : Nat) : f n < step f n :=
  Forest.oracle_lt_reflect (fun _ => f) n 0 (Nat.zero_le n)

/-- At limits every child remains a separately accessible oracle. -/
def stage : BTree → Nat → Nat
  | .zero => step Nat.succ
  | .succ a => step (stage a)
  | .lim children => Forest.reflect (fun i => stage (children i))
termination_by structural a => a

theorem stage_succ_gt (a : BTree) (n : Nat) : stage a n < stage (.succ a) n :=
  self_lt_step (stage a) n

theorem stage_child_lt_limit (children : Nat → BTree) (n i : Nat) (hi : i ≤ n) :
    stage (children i) n < stage (.lim children) n :=
  Forest.oracle_lt_reflect (fun j => stage (children j)) n i hi

theorem contender5_lt_stage (a : BTree) : Original.contender5 < stage a 42 := by
  cases a with
  | zero => exact Forest.contender5_lt_reflect (fun _ => Nat.succ)
  | succ a => exact Forest.contender5_lt_reflect (fun _ => stage a)
  | lim children => exact Forest.contender5_lt_reflect (fun i => stage (children i))

/-- Successor spines are exactly successive function-level reflections. -/
theorem pad_stage_eq_reflectIter (a : BTree) (k : Nat) :
    stage (Hierarchy.pad a k) = Hierarchy.reflectIter step k (stage a) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg step ih

theorem pad_stage_apply (a : BTree) (k n : Nat) :
    stage (Hierarchy.pad a k) n = Hierarchy.reflectIter step k (stage a) n :=
  congrFun (pad_stage_eq_reflectIter a k) n

/-- The same tree syntax supports a diagonal over all finite reflection levels. -/
theorem reflectIter_lt_diagonal (a : BTree) (n i : Nat) (hi : i ≤ n) :
    Hierarchy.reflectIter step (i + 1) (stage a) n <
      stage (Hierarchy.diagonalTree a) n := by
  have h := stage_child_lt_limit (fun k => Hierarchy.pad a (k + 1)) n i hi
  rw [pad_stage_apply] at h
  exact h

theorem fixed_reflection_lt_diagonal (a : BTree) (n k : Nat) (hk : k ≤ n + 1) :
    Hierarchy.reflectIter step k (stage a) n < stage (Hierarchy.diagonalTree a) n :=
  Nat.lt_of_le_of_lt
    (Hierarchy.reflectIter_mono step self_lt_step (stage a) n k (n + 1) hk)
    (reflectIter_lt_diagonal a n n (Nat.le_refl n))

theorem step_growth {n : Nat} {a b : BTree} (h : Hierarchy.Step n a b) :
    stage a n < stage b n := by
  cases h with
  | succ a => exact stage_succ_gt a n
  | limit children i hi => exact stage_child_lt_limit children n i hi

theorem path_growth {n : Nat} {a b : BTree} {k : Nat}
    (h : Hierarchy.Path n a b k) : stage a n + k ≤ stage b n := by
  induction h with
  | refl => exact Nat.le_refl _
  | extend path edge ih => exact Nat.le_trans (Nat.succ_le_succ ih) (step_growth edge)

/-- The hierarchy distinguishes these two raw presentations of ordinal zero. -/
theorem rank_zero_presentations_differ (n : Nat) :
    stage .zero n < stage (.lim (fun _ => .zero)) n :=
  stage_child_lt_limit (fun _ => .zero) n 0 (Nat.zero_le n)

end ForestHierarchy
