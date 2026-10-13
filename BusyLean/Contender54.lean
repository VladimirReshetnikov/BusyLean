import BusyLean.Contender53

/-!
# Contender 54: reflection as a primitive

```
contender_54 := F54 (F54 42)
F54 n        := hier (numReflect N family53) T N
                where N = family53 n, T = stackTree N
```

Contender 53 iterates ladder reflection along one fixed tree, one particular
recursion. Here reflection is a primitive of the language of Contender 51,

  `reflT : tree → (nat → nat) → nat → nat`, `reflT t g = ladderReflect g t`,

next to the number oracle `g : nat → nat` and all of Contender 51's tree
primitives. Closed programs of type `nat` can build trees with the jumps,
collapses and iteration operators, reflect over **any** tree they build,
and iterate this at higher types. `reflAlong` is one such program.
`numReflect N g m` exceeds `g m` and every closed `nat` program of size
`<= m`.

**Do not evaluate `contender_54`.**
-/

namespace BusyLean

open Ordinal (CTree)
open Ordinal.TL (Ty)

/-- Contender 51's primitives, then `reflT` and the number oracle. -/
def prims54 : List Ty :=
  prims51 ++ [.arr .tree (.arr (.arr .nat .nat) (.arr .nat .nat)), .arr .nat .nat]

/-- The values of the primitives at depth `N` with number oracle `g`. -/
def primEnv54 (N : Nat) (g : Nat → Nat) : Ordinal.TL.Env prims54 :=
  (levelIterTree N, metaJump N, closeU N, thetaFrom N, iterOf,
    fun t h => ladderReflect h t, g, ())

/-- Reflection over all closed `nat` programs over the primitives. -/
def numReflect (N : Nat) (g : Nat → Nat) (m : Nat) : Nat :=
  m + 1 + BigNumber.maxN (g m) (BigNumber.maximum id (Ordinal.PTL.natsUpTo prims54 (primEnv54 N g) m))

/-- Contender 53's construction as a function of its input: `family53 42 = contender_53`. -/
def family53 (n : Nat) : Nat := F53 (F53 n)

/-- The hierarchy along the stacked tree, based on the programmable reflection. -/
def F54 (n : Nat) : Nat :=
  Ordinal.hier (numReflect (family53 n) family53) (stackTree (family53 n)) (family53 n)

/-- **Contender 54.** Never evaluate it. -/
def contender_54 : Nat := F54 (F54 42)

end BusyLean
