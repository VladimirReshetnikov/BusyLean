import BusyLean.Ordinal.RelLevels
import BusyLean.Contender43

/-!
# Contender 44: collapsing closures with tree-indexed levels

```
contender_44 := F44 (F44 42)
F44 n        := hier family43 (levelTree44 (family43 n)) (family43 n)
```

Contender 43's first-class closure collapses relative to an operator with
finitely many levels `Ω_k`. `Ordinal.DLJ` (Contender 26's collapse with levels
indexed by trees, relativized to an operator `J`) gives a stronger closure:
`relLevelRounds J N t` iterates `Λ ↦ ψ^J₀(ε_{Ω_Λ+1})` `N` times from `t`. Each
round's level index is the previous round's tree, climbing toward fixed points
of `α ↦ ψ^J₀(Ω_α)` relative to `J`.

The closure `closeL N J t` joins language closure, the finite-level relative
collapse, and these rounds. Metalanguages with this closure are stacked
(`metaBoostC`) to the height of Contender 43's tree over the meta-jump.

**Do not evaluate `contender_44`.**
-/

namespace BusyLean

/-- Contender 43's construction as a function of its input: `family43 42 = contender_43`. -/
def family43 (n : Nat) : Nat := F43 (F43 n)

/-- Language closure, relative collapse, and relative level rounds. -/
def closeL (N : Nat) (J : Ordinal.CTree → Ordinal.CTree) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then closeC N J t
    else Ordinal.relLevelRounds J N (Ordinal.relCollapse J N t)

/-- Contender 43's tree, closed under metalanguages with the level-collapsing closure. -/
def levelTree44 (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then collapseTree43 N
    else Ordinal.metaBoostC (closeL N) (collapseTree43 N) (metaJump N) (collapseTree43 N)

/-- The hierarchy along the tree, based on Contender 43's family. -/
def F44 (n : Nat) : Nat := Ordinal.hier family43 (levelTree44 (family43 n)) (family43 n)

/-- **Contender 44.** Never evaluate it. -/
def contender_44 : Nat := F44 (F44 42)

end BusyLean
