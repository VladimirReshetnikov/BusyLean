import BusyLean.Ordinal.PrimLanguage
import BusyLean.Contender50

/-!
# Contender 51: programs over the iteration operators

```
contender_51 := F51 (F51 42)
F51 n        := hier (ladderReflect family50 T) T N
                where N = family50 n, T = primTree N
```

Contenders 45-48 apply the iteration operators along trees chosen from outside:
`thetaFrom`, `iterOf`, and the level hierarchy `iterLevel`. Here they are
primitives of a language (`Ordinal.PTL`, System T over trees with an
environment of primitives):

* `seed : tree` (Contender 48's tree), `metaJump : tree → tree`,
* `closeU : (tree → tree) → tree → tree` (the universe-collapsing closure),
* `thetaFrom : Φ`, with `Φ = (tree → tree) → tree → tree → tree`,
* `iterOf : Φ → Φ`.

So `iterLevel k = treeRec thetaFrom iterOf (pointwise lim) k` is a program.
Programs can apply it at levels, heights and arguments they compute, nest
these choices, and diagonalize. The tree joins all closed tree programs of
every size. The number is read off by Contender 50's ladder reflection.

**Do not evaluate `contender_51`.**
-/

namespace BusyLean

open Ordinal (CTree)
open Ordinal.TL (Ty)

/-- `Φ = (tree → tree) → tree → tree → tree`: a base turned into an iteration. -/
def phiTy : Ty := .arr (.arr .tree .tree) (.arr .tree (.arr .tree .tree))

/-- The primitive types: seed, meta-jump, closure, `thetaFrom`, `iterOf`. -/
def prims51 : List Ty :=
  [.tree, .arr .tree .tree, .arr (.arr .tree .tree) (.arr .tree .tree), phiTy, .arr phiTy phiTy]

/-- Contender 50's construction as a function of its input: `family50 42 = contender_50`. -/
def family50 (n : Nat) : Nat := F50 (F50 n)

/-- The values of the primitives at depth `N`. -/
def primEnv51 (N : Nat) : Ordinal.TL.Env prims51 :=
  (levelIterTree N, metaJump N, closeU N, thetaFrom N, iterOf, ())

/-- Contender 48's tree joined with every closed tree program over the primitives. -/
def primTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then levelIterTree N else Ordinal.primLangTree prims51 (primEnv51 N)

/-- The hierarchy along the program tree, based on ladder reflection over it. -/
def F51 (n : Nat) : Nat :=
  Ordinal.hier (ladderReflect family50 (primTree (family50 n))) (primTree (family50 n)) (family50 n)

/-- **Contender 51.** Never evaluate it. -/
def contender_51 : Nat := F51 (F51 42)

end BusyLean
