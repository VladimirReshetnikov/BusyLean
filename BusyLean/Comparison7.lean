import BusyLean.Contender7
import BusyLean.Comparison

/-!
# Contender 7 comparison theorems

Every comparison is by explicit inclusion; no monotonicity of reflection is
assumed.  That is important because a reflected program may inspect and branch
on oracle values, so reflection is not monotone in its oracle in general.

Branch zero is definitionally Contender 6's entire self-generated index.  Every
successor branch contains the preceding branch as child zero and its autonomous
payload as child one.  At input 42 the outer root sees branch 42, yielding a
kernel-checked chain of 43 strict reflection steps above the old index (42 guard
steps plus the outer root), while also exposing the level-41 autonomous payload.
-/

namespace BusyLean

open BusyLean.W

/-- Every branch visible at input `n` is strictly below the Contender 7 family. -/
theorem contender7_branch_lt {i n : Nat} (hi : i <= n) :
    stage p5Family (contender7Branch i) n < contender7Family n :=
  stage_child_lt p5Family contender7Branch hi

/-- The old self-generated index is branch zero. -/
theorem contender7_branch_zero : contender7Branch 0 = index := rfl

/-- Each guarded branch is strictly below its successor, at every input. -/
theorem contender7_branch_step_lt (k n : Nat) :
    stage p5Family (contender7Branch k) n <
      stage p5Family (contender7Branch (k + 1)) n := by
  change stage p5Family (contender7Branch k) n <
    stage p5Family
      (.node (fun i =>
        match i with
        | 0 => contender7Branch k
        | _ + 1 => contender7RawBranch k)) n
  exact stage_child_lt p5Family _ (Nat.zero_le n)

/-- The autonomous payload at level `k` is child one of guarded branch `k+1`. -/
theorem contender7_raw_lt_next (k : Nat) {n : Nat} (hn : 1 <= n) :
    stage p5Family (contender7RawBranch k) n <
      stage p5Family (contender7Branch (k + 1)) n := by
  change stage p5Family (contender7RawBranch k) n <
    stage p5Family
      (.node (fun i =>
        match i with
        | 0 => contender7Branch k
        | _ + 1 => contender7RawBranch k)) n
  exact stage_child_lt p5Family _ hn

/-- Iterating the previous theorem gives a strict path from branch zero through
any requested finite number of guarded branches. -/
theorem contender7_branch_zero_lt_succ :
    forall k n : Nat,
      stage p5Family (contender7Branch 0) n <
        stage p5Family (contender7Branch (k + 1)) n
  | 0, n => contender7_branch_step_lt 0 n
  | k + 1, n =>
      Nat.lt_trans (contender7_branch_zero_lt_succ k n)
        (contender7_branch_step_lt (k + 1) n)

/-- The 42 guarded steps give a strict lower bound before the outer root is even
applied. -/
theorem finalFamily_lt_contender7Branch42 :
    finalFamily 42 < stage p5Family (contender7Branch 42) 42 := by
  change stage p5Family (contender7Branch 0) 42 <
    stage p5Family (contender7Branch (41 + 1)) 42
  exact contender7_branch_zero_lt_succ 41 42

/-- Branch 42 is visible to the outer root at input 42. -/
theorem contender7Branch42_lt_contender_7 :
    stage p5Family (contender7Branch 42) 42 < contender_7 :=
  contender7_branch_lt (Nat.le_refl 42)

/-- At every input, the direct branch-zero inclusion already puts the old family
below the new family. -/
theorem finalFamily_lt_contender7Family (n : Nat) :
    finalFamily n < contender7Family n :=
  contender7_branch_lt (Nat.zero_le n)

/-- **Required comparison:** Contender 6 is strictly below Contender 7.  The
chosen proof records the full 42-step guard margin rather than taking the direct
branch-zero shortcut. -/
theorem contender_6_lt_contender_7 : contender_6 < contender_7 :=
  Nat.lt_trans finalFamily_lt_contender7Branch42
    contender7Branch42_lt_contender_7

/-- The exact Lean port of Contender 5 is also strictly below Contender 7. -/
theorem contender_5_lt_contender_7 : contender_5 < contender_7 :=
  Nat.lt_trans contender_5_lt_contender_6 contender_6_lt_contender_7

/-- The level-41 autonomous payload is strictly below guarded branch 42. -/
theorem hyper41_lt_contender7Branch42 :
    stage p5Family
      (Autonomous.realize
        (Autonomous.hyper 41
          (Autonomous.OTree.succ contender7Base))) 42 <
      stage p5Family (contender7Branch 42) 42 := by
  change stage p5Family (contender7RawBranch 41) 42 <
    stage p5Family (contender7Branch (41 + 1)) 42
  exact contender7_raw_lt_next 41 (Nat.succ_le_succ (Nat.zero_le 41))

/-- The highest autonomous payload selected by input 42 is strictly below the
final contender. -/
theorem hyper41_lt_contender_7 :
    stage p5Family
      (Autonomous.realize
        (Autonomous.hyper 41
          (Autonomous.OTree.succ contender7Base))) 42 < contender_7 :=
  Nat.lt_trans hyper41_lt_contender7Branch42
    contender7Branch42_lt_contender_7

end BusyLean
