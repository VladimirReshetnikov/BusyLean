import BusyLean.Contender67

/-!
# Contender 68: programs over the reflective tower's step

```
contender_68 := F68 (F68 42)
F68 n        := hier (cwStepClosure N family67) (cwStepTree N) N
```

Contender 67's tower of closure operators has a uniform step,

  `cwStep X H` = the closures of Contender 66's language plus `H` and `X`,

with `cwTower (a+1) = cwStep (cwTower a)`. Here the step and the tower are
values of the language:

* `cwStep : cwTy → cwTy`, with `cwTy = (tree → C) → C`;
* `cwAt : tree → cwTy`, the reflective tower at any program-chosen height.

Programs iterate `cwStep` from any operator they build (not only from
`cwTower 0`), along trees they build, diagonalize, and feed one tower into
another. These join Contender 66's primitives.

**Do not evaluate `contender_68`.**
-/

namespace BusyLean

open Ordinal (CTree Closures)
open Ordinal.PTL2 (Ty)

/-- One level of the reflective tower, from any closure operator `X`. -/
def cwStep (N : Nat) (g : Nat → Nat) (X : (CTree → Closures) → Closures) (H : CTree → Closures) :
    Closures :=
  (Ordinal.ptl2Lift (famTy :: cwTy :: prims66) (H, X, primEnv66 N g),
   Ordinal.num2Lift (famTy :: cwTy :: prims66) (H, X, primEnv66 N g))

/-- Contender 66's primitives plus the step and the tower. -/
def prims68 : List Ty := .arr cwTy cwTy :: .arr .tree cwTy :: prims66

def primEnv68 (N : Nat) (g : Nat → Nat) : Ordinal.PTL2.Env prims68 :=
  (cwStep N g, cwTower N g, primEnv66 N g)

/-- Contender 67's construction as a function of its input: `family67 42 = contender_67`. -/
def family67 (n : Nat) : Nat := F67 (F67 n)

/-- Contender 67's tree, joined with the meta-jump's closure under this language. -/
def cwStepTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then cwTree N
    else Ordinal.ptl2Lift prims68 (primEnv68 N family67) (metaJump N) (cwTree N)

/-- The language's number closure over the oracle `g`. -/
def cwStepClosure (N : Nat) (g : Nat → Nat) : Nat → Nat :=
  Ordinal.num2Lift prims68 (primEnv68 N g) g

/-- The hierarchy along the tree, based on the language's number closure. -/
def F68 (n : Nat) : Nat :=
  Ordinal.hier (cwStepClosure (family67 n) family67) (cwStepTree (family67 n)) (family67 n)

/-- **Contender 68.** Never evaluate it. -/
def contender_68 : Nat := F68 (F68 42)

end BusyLean
