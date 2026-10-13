import BusyLean.Contender7
import BusyLean.Comparison

/-!
# Contender 7 comparison theorems

The comparison uses an explicit inclusion, never monotonicity of reflection.
Branch zero of `contender7Index` is definitionally `index`, the entire schedule
used by Contender 6.  A parent stage strictly exceeds every visible child stage.
-/

namespace BusyLean

open BusyLean.W

/-- Every branch visible at input `n` is strictly below the Contender 7 family. -/
theorem contender7_branch_lt {i n : Nat} (hi : i <= n) :
    stage p5Family (contender7Branch i) n < contender7Family n :=
  stage_child_lt p5Family contender7Branch hi

/-- The old self-generated index is branch zero. -/
theorem contender7_branch_zero : contender7Branch 0 = index := rfl

/-- At every input, the Contender 6 family is strictly below the new family. -/
theorem finalFamily_lt_contender7Family (n : Nat) :
    finalFamily n < contender7Family n :=
  contender7_branch_lt (Nat.zero_le n)

/-- **Required comparison:** Contender 6 is strictly below Contender 7. -/
theorem contender_6_lt_contender_7 : contender_6 < contender_7 :=
  finalFamily_lt_contender7Family 42

/-- The exact Lean port of Contender 5 is also strictly below Contender 7. -/
theorem contender_5_lt_contender_7 : contender_5 < contender_7 :=
  Nat.lt_trans contender_5_lt_contender_6 contender_6_lt_contender_7

/-- At input 42 the highest branch guaranteed directly by the prefix argument
is branch 42, i.e. the 41st higher derivative of the autonomous closure. -/
theorem hyper41_lt_contender_7 :
    stage p5Family
      (Autonomous.realize
        (Autonomous.hyper 41
          (Autonomous.OTree.succ contender7Base))) 42 < contender_7 :=
  contender7_branch_lt (Nat.le_refl 42)

end BusyLean
