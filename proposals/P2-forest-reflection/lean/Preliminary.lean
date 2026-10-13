import Arboreal
import Hierarchy

/-!
# Preliminary contender: arboreal finite-type reflection

The entry is a closed constructive natural number. It does not reference
`Original.contender5`; that name occurs only in the comparison theorems.

The seed `treeIndex` diagonally ranges over all finite functional levels of a
raw Brouwer-tree schedule. The final limit gives a proved margin: its value at
input n exceeds n+1 successive applications of the arboreal-language reflection
operator to the entire seed hierarchy. This yields 43 reflections at input 42.
No interpretation of raw tree equality as ordinal equality is assumed.
-/

/-- A final limit whose visible children contain longer reflection spines. -/
def contestTree : BTree := Hierarchy.diagonalTree treeIndex

/-- The whole family diagonally exceeds each fixed finite reflection height. -/
def contenderFamily (n : Nat) : Nat := Hierarchy.stage Arboreal.Rw contestTree n

/-- The competition entry. Do not attempt to evaluate its decimal expansion. -/
def preliminaryContender : Nat := contenderFamily 42

/-- Every stage already strictly exceeds the exact source Contender 5 at 42. -/
theorem contender_5_lt_stage (a : BTree) :
    Original.contender5 < Hierarchy.stage Arboreal.Rw a 42 :=
  Hierarchy.lower_bound_at Arboreal.Rw Original.contender5 42
    Arboreal.contender5_lt_Rw a

/-- The required comparison, checked by Lean's kernel without axioms. -/
theorem contender_5_lt_preliminaryContender : Original.contender5 < preliminaryContender :=
  contender_5_lt_stage contestTree

/-- Every finite reflection height visible to the final join is dominated. -/
theorem visible_reflections_lt_contenderFamily (n i : Nat) (hi : i ≤ n) :
    Hierarchy.reflectIter Arboreal.Rw (i + 1)
      (Hierarchy.stage Arboreal.Rw treeIndex) n < contenderFamily n :=
  Hierarchy.reflectIter_lt_diagonal Arboreal.Rw Arboreal.self_lt_Rw treeIndex n i hi

/-- At input n the family exceeds n+1 full applications of reflection. -/
theorem diagonal_reflections_lt_contenderFamily (n : Nat) :
    Hierarchy.reflectIter Arboreal.Rw (n + 1)
      (Hierarchy.stage Arboreal.Rw treeIndex) n < contenderFamily n :=
  visible_reflections_lt_contenderFamily n n (Nat.le_refl n)

/-- Every fixed finite reflection level is eventually exceeded. -/
theorem fixed_reflection_lt_contenderFamily (n k : Nat) (hk : k ≤ n + 1) :
    Hierarchy.reflectIter Arboreal.Rw k
      (Hierarchy.stage Arboreal.Rw treeIndex) n < contenderFamily n :=
  Hierarchy.fixed_reflection_lt_diagonal Arboreal.Rw Arboreal.self_lt_Rw
    treeIndex n k hk

/-- Each child visible at input 42 is strictly dominated. -/
theorem visible_reflections_lt_preliminaryContender (i : Nat) (hi : i ≤ 42) :
    Hierarchy.reflectIter Arboreal.Rw (i + 1)
      (Hierarchy.stage Arboreal.Rw treeIndex) 42 < preliminaryContender :=
  visible_reflections_lt_contenderFamily 42 i hi

/-- In particular, the entry beats 43 successive full expressive reflections. -/
theorem forty_three_reflections_lt_preliminaryContender :
    Hierarchy.reflectIter Arboreal.Rw 43
      (Hierarchy.stage Arboreal.Rw treeIndex) 42 < preliminaryContender :=
  diagonal_reflections_lt_contenderFamily 42

/-- A numerical gap, weaker than the preceding function-level description. -/
theorem seed_plus_44_le_preliminaryContender :
    Hierarchy.stage Arboreal.Rw treeIndex 42 + 44 ≤ preliminaryContender :=
  Hierarchy.diagonal_gap_at Arboreal.Rw Arboreal.self_lt_Rw treeIndex 42 44 rfl

/-- The exact baseline is separated by at least 45 natural-number units. -/
theorem contender_5_plus_45_le_preliminaryContender :
    Original.contender5 + 45 ≤ preliminaryContender :=
  Hierarchy.lower_bound_diagonal_gap_at Arboreal.Rw Arboreal.self_lt_Rw
    treeIndex 42 Original.contender5 45 (contender_5_lt_stage treeIndex) rfl

/-- Equal set-theoretic ordinal ranks do not identify hierarchy values. -/
theorem rank_zero_presentations_differ (n : Nat) :
    Hierarchy.stage Arboreal.Rw .zero n <
      Hierarchy.stage Arboreal.Rw (.lim (fun _ => .zero)) n :=
  Hierarchy.zero_lt_constant_zero_limit Arboreal.Rw Arboreal.self_lt_Rw n
