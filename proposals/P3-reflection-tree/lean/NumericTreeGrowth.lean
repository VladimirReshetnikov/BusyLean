import TreeGrowth
import TreeMargin

/-! Instantiation of the abstract tree-growth results for the actual hierarchy. -/

namespace Biggest

theorem numeric_successor_growth (n : Nat) (a : Stage) :
    hierarchy a n < hierarchy (.succ a) n :=
  reflect_gt_oracle (hierarchy a) n

theorem numeric_limit_zero_growth (n : Nat) (s : Nat → Stage) :
    hierarchy (s 0) n < hierarchy (.lim s) n :=
  Nat.lt_succ_of_le
    (le_maximum_of_mem (fun k => hierarchy (s k) n) 0
      (natsUpTo (n + 1)) (margin_zero_mem n))

theorem numeric_higherTower_growth (n : Nat) (f : Stage → Stage) (a : Stage) :
    hierarchy a n < hierarchy (higherTower f a) n :=
  higherTower_increases (fun a => hierarchy a n)
    (numeric_successor_growth n) (numeric_limit_zero_growth n) f a

theorem numeric_promotion_growth (n : Nat) (f : Stage → Stage) (a : Stage) :
    hierarchy a n < hierarchy (promoteTreeFunction f a) n :=
  promoteTreeFunction_increases (fun a => hierarchy a n)
    (numeric_successor_growth n) (numeric_limit_zero_growth n) f a

theorem numeric_promoted_growth (n : Nat) (a : Stage) :
    hierarchy a n < hierarchy (promotedTreeFunction a) n :=
  promotedTreeFunction_increases (fun a => hierarchy a n)
    (numeric_successor_growth n) (numeric_limit_zero_growth n) a

theorem numeric_finalStage_growth (n : Nat) :
    hierarchy gammaTree n < hierarchy finalStage n :=
  finalStage_exceeds_gammaTree (fun a => hierarchy a n)
    (numeric_successor_growth n) (numeric_limit_zero_growth n)

end Biggest
