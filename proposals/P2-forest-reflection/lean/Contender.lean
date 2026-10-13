import Preliminary
import ForestHierarchy

/-!
# Final Contender 6: a forest reflection over both complete constructions

The oracle at index zero is the preliminary reflection family. Positive
indices enumerate successor reflection spines above the full forest hierarchy
at the same closed tree. The final finite-language reflection therefore beats
both routes by explicit oracle inclusion; no monotonicity assumption about
changing a reflection language or changing its oracles is needed.

The competition entry uses no previous contender constant in its definition.
-/

/-- Preserve the preliminary family and every positive forest reflection level. -/
def finalOracles : Forest.Oracles
  | 0 => contenderFamily
  | k + 1 => ForestHierarchy.stage (Hierarchy.pad contestTree k)

/-- The final family remains a constructive total function of its argument. -/
def finalFamily (n : Nat) : Nat := Forest.reflect finalOracles n

/-- The closed competition entry, with all syntax budgets fixed by input 42. -/
def contender_6 : Nat := finalFamily 42

/-- The final family pointwise exceeds the completed preliminary family. -/
theorem preliminary_lt_finalFamily (n : Nat) : contenderFamily n < finalFamily n :=
  Forest.oracle_lt_reflect finalOracles n 0 (Nat.zero_le n)

theorem preliminary_lt_contender_6 : preliminaryContender < contender_6 :=
  preliminary_lt_finalFamily 42

/-- The required strict comparison with the exact port of source Contender 5. -/
theorem contender_5_lt_contender_6 : Original.contender5 < contender_6 :=
  Nat.lt_trans contender_5_lt_preliminaryContender preliminary_lt_contender_6

/-- An independent comparison follows from the final reflector alone. -/
theorem contender_5_lt_contender_6_direct : Original.contender5 < contender_6 :=
  Forest.contender5_lt_reflect finalOracles

/-- Each forest successor spine whose oracle index fits the argument is beaten. -/
theorem forest_padding_lt_finalFamily (n k : Nat) (hk : k + 1 ≤ n) :
    ForestHierarchy.stage (Hierarchy.pad contestTree k) n < finalFamily n :=
  Forest.oracle_lt_reflect finalOracles n (k + 1) hk

/-- The same margin expressed as exact iteration of the forest reflector. -/
theorem forest_reflections_lt_finalFamily (n k : Nat) (hk : k + 1 ≤ n) :
    Hierarchy.reflectIter ForestHierarchy.step k
      (ForestHierarchy.stage contestTree) n < finalFamily n :=
  Eq.mp
    (congrArg (fun value : Nat => value < finalFamily n)
      (ForestHierarchy.pad_stage_apply contestTree k n))
    (forest_padding_lt_finalFamily n k hk)

/-- Index 42 carries 41 further forest reflections above the full contest tree. -/
theorem forest_stage_41_lt_contender_6 :
    ForestHierarchy.stage (Hierarchy.pad contestTree 41) 42 < contender_6 :=
  forest_padding_lt_finalFamily 42 41 (by decide)

theorem forty_one_forest_reflections_lt_contender_6 :
    Hierarchy.reflectIter ForestHierarchy.step 41
      (ForestHierarchy.stage contestTree) 42 < contender_6 :=
  forest_reflections_lt_finalFamily 42 41 (by decide)

/-- The final entry also preserves the first route's certified 43-level margin. -/
theorem forty_three_arboreal_reflections_lt_contender_6 :
    Hierarchy.reflectIter Arboreal.Rw 43
      (Hierarchy.stage Arboreal.Rw treeIndex) 42 < contender_6 :=
  Nat.lt_trans forty_three_reflections_lt_preliminaryContender
    preliminary_lt_contender_6

/-- No single fixed program in the final oracle language defines this family. -/
theorem finalFamily_not_representable (t : Forest.Expr) :
    ¬ (∀ n, Forest.eval finalOracles n t = finalFamily n) :=
  Forest.reflect_not_representable finalOracles t
