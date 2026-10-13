import BusyLean.Contender65

/-!
# Contender 66: programs over closure and towering

```
contender_66 := F66 (F66 42)
F66 n        := hier (closeClosure N family65) (closeTree N) N
```

Contender 65's hierarchy of step operators is built from two operations:
closing a language with an extra family of closures, and towering a step along
a tree. Here both are values of the language (`PTL2`, with products):

* `closeWith : (tree → C) → C`, the closure pair of Contender 61's language plus
  any family a program supplies;
* `towerFrom : (C → C) → C → tree → C`, towering any step a program defines.

`metaStep S c = closeWith (towerFrom S c)` is then a program. Contender 65's
`metaS` is a tree recursion at type `C → C`. Programs can also diagonalize
across meta-levels, feed towers of one hierarchy into another, and iterate at
higher types. These join Contender 61's primitives. The tree joins Contender
65's tree with the meta-jump's closure under this language, whose number
closure is the hierarchy's base.

**Do not evaluate `contender_66`.**
-/

namespace BusyLean

open Ordinal (CTree Closures)
open Ordinal.PTL2 (Ty)

/-- Steps on closure pairs. -/
def stepTy : Ty := .arr closTy closTy

/-- Contender 61's primitives plus closure-with-a-family and towering. -/
def prims66 : List Ty := .arr famTy closTy :: .arr stepTy (.arr closTy famTy) :: prims61

def primEnv66 (N : Nat) (g : Nat → Nat) : Ordinal.PTL2.Env prims66 :=
  (fun H => (Ordinal.ptl2Lift (famTy :: prims61) (H, primEnv61 N g),
             Ordinal.num2Lift (famTy :: prims61) (H, primEnv61 N g)),
   fun S c => towerFrom S c,
   primEnv61 N g)

/-- Contender 65's construction as a function of its input: `family65 42 = contender_65`. -/
def family65 (n : Nat) : Nat := F65 (F65 n)

/-- Contender 65's tree, joined with the meta-jump's closure under this language. -/
def closeTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then metaSTree N
    else Ordinal.ptl2Lift prims66 (primEnv66 N family65) (metaJump N) (metaSTree N)

/-- The language's number closure over the oracle `g`. -/
def closeClosure (N : Nat) (g : Nat → Nat) : Nat → Nat :=
  Ordinal.num2Lift prims66 (primEnv66 N g) g

/-- The hierarchy along the tree, based on the language's number closure. -/
def F66 (n : Nat) : Nat :=
  Ordinal.hier (closeClosure (family65 n) family65) (closeTree (family65 n)) (family65 n)

/-- **Contender 66.** Never evaluate it. -/
def contender_66 : Nat := F66 (F66 42)

end BusyLean
