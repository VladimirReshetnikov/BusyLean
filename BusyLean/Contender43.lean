import BusyLean.Contender42

/-!
# Contender 43: collapse as a first-class closure

```
contender_43 := F43 (F43 42)
F43 n        := hier family42 (collapseTree43 (family42 n)) (family42 n)
```

Contender 42 collapsed relative to one fixed operator, the meta-jump. P27's
metalanguage takes its closure operator `lift : (tree → tree) → tree → tree`
as a parameter, and Contender 40 used `langLift`, the closure of an operator
under System T over trees. Here the base closure also **collapses**:

  `closeC N J t = lim (langLift J t, relCollapse J N t)`.

`metaBoostC` stacks metalanguages along a tree with this closure at level 0.
At level 1, programs build operators from the meta-jump, collapse relative to
them, and iterate the results by tree recursion. At level `a+1`, programs call
the whole closure of level `a` as a first-class value, so they can collapse
relative to collapses.

**Do not evaluate `contender_43`.**
-/

namespace BusyLean.Ordinal

/-- Metalanguages stacked along a tree, with the closure operator `L0` at level 0. -/
def metaBoostC (L0 : (CTree → CTree) → CTree → CTree) :
    CTree → (CTree → CTree) → CTree → CTree
  | .zero => L0
  | .succ a => metaLangLift (metaBoostC L0 a)
  | .lim f => fun b t => .lim fun i => metaBoostC L0 (f i) b t
  | .supL _ => L0
  | .supH _ => L0

end BusyLean.Ordinal

namespace BusyLean

/-- Contender 42's construction as a function of its input: `family42 42 = contender_42`. -/
def family42 (n : Nat) : Nat := F42 (F42 n)

/-- Language closure joined with collapse relative to the operator. -/
def closeC (N : Nat) (J : Ordinal.CTree → Ordinal.CTree) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i => if i = 0 then Ordinal.langLift J t else Ordinal.relCollapse J N t

/-- Contender 42's tree, closed under collapsing metalanguages over the meta-jump,
stacked to its own height. -/
def collapseTree43 (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then collapseTree N
    else Ordinal.metaBoostC (closeC N) (collapseTree N) (metaJump N) (collapseTree N)

/-- The hierarchy along the tree, based on Contender 42's family. -/
def F43 (n : Nat) : Nat := Ordinal.hier family42 (collapseTree43 (family42 n)) (family42 n)

/-- **Contender 43.** Never evaluate it. -/
def contender_43 : Nat := F43 (F43 42)

end BusyLean
