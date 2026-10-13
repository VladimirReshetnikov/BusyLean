import BusyLean.Ordinal.PrimLanguage2
import BusyLean.Contender60

/-!
# Contender 61: programs over the tower operators

```
contender_61 := F61 (F61 42)
F61 n        := hier (towerProgClosure N family60) (towerProgTree N) N
```

Contenders 57-60 each turn one construction into a primitive, or iterate it
along a tree chosen from outside. `PTL2` (System T over trees with products
and primitives) lets programs handle closure pairs
`C = ((tree → tree) → tree → tree) × ((nat → nat) → nat → nat)` as values.
Contender 61's primitives:

* the seed tree (Contender 60's tree), the meta-jump, the number oracle, and
  reflection `reflT : tree → (nat → nat) → nat → nat`;
* `towerT : tree → C`, Contender 59's tower;
* `towerH : (tree → C) → tree → C`, the operator of Contender 60.

So `upLevels k = treeRec towerT towerH (limit) k` is a program, and programs
can apply `towerH` to families they build themselves, at levels and heights
they compute, at higher types. The tree joins Contender 60's tree with the
meta-jump's closure under this language, whose number closure is the base of
the hierarchy.

**Do not evaluate `contender_61`.**
-/

namespace BusyLean

open Ordinal (CTree)
open Ordinal.PTL2 (Ty)

/-- `(tree → tree) → tree → tree`. -/
def liftT2 : Ty := .arr (.arr .tree .tree) (.arr .tree .tree)
/-- `(nat → nat) → nat → nat`. -/
def liftN2 : Ty := .arr (.arr .nat .nat) (.arr .nat .nat)
/-- Closure pairs. -/
def closTy : Ty := .prod liftT2 liftN2
/-- Height-indexed families of closure pairs. -/
def famTy : Ty := .arr .tree closTy

/-- The primitive types. -/
def prims61 : List Ty :=
  [.tree, .arr .tree .tree, .arr .nat .nat, .arr .tree (.arr (.arr .nat .nat) (.arr .nat .nat)),
   famTy, .arr famTy famTy]

/-- The primitive values at depth `N` with number oracle `g`. -/
def primEnv61 (N : Nat) (g : Nat → Nat) : Ordinal.PTL2.Env prims61 :=
  (upTree N, metaJump N, g, fun t h => ladderReflect h t,
   Ordinal.towerT prims54 (primEnv54 N g), Ordinal.towerH prims54 (primEnv54 N g), ())

/-- Contender 60's construction as a function of its input: `family60 42 = contender_60`. -/
def family60 (n : Nat) : Nat := F60 (F60 n)

/-- Contender 60's tree, joined with the meta-jump's closure under the tower language. -/
def towerProgTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then upTree N
    else Ordinal.ptl2Lift prims61 (primEnv61 N family60) (metaJump N) (upTree N)

/-- The number closure of the tower language over the oracle `g`. -/
def towerProgClosure (N : Nat) (g : Nat → Nat) : Nat → Nat :=
  Ordinal.num2Lift prims61 (primEnv61 N g) g

/-- The hierarchy along the tree, based on the tower language's number closure. -/
def F61 (n : Nat) : Nat :=
  Ordinal.hier (towerProgClosure (family60 n) family60) (towerProgTree (family60 n)) (family60 n)

/-- **Contender 61.** Never evaluate it. -/
def contender_61 : Nat := F61 (F61 42)

end BusyLean
