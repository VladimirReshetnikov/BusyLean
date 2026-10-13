import BusyLean.Contender38

/-!
# Contender 39: mixing the impredicative jump with predicative collapse

```
contender_39 := F39 (F39 42)
F39 n        := hier family38 (mixTree (family38 n)) (family38 n)
```

`jumpTree` stacks System T over trees on the impredicative jump alone, so its
language levels can never call Contender 31's predicative operator `boost31`
(collapsing with tree-indexed levels, universes, and closure functionals of
transfinite type). Here the primitive does both: `mixed N t` is the limit of
`jump N t` and `boost31 (jump N t)`. The stacked languages over `mixed N`
interleave the two operators at every level.

The depth parameter of every enumeration in the tree (System FT programs,
ladder programs, bootstrap steps) is `family38 n`, not `n`. The hierarchy
`hier` (Contender 38) turns the tree into a number, with base Contender 38's
family.

**Do not evaluate `contender_39`.**
-/

namespace BusyLean

/-- The impredicative jump followed by Contender 31's predicative operator. -/
def mixed (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i => if i = 0 then jump N t else Ordinal.boost31 (jump N t)

/-- Languages stacked over the mixed primitive, to the height of Contender 37's tree. -/
def mixTree (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then jumpTree N else Ordinal.stackOver (mixed N) (jumpTree N) (jumpTree N)

/-- Contender 38's construction as a function of its input: `family38 42 = contender_38`. -/
def family38 (n : Nat) : Nat := F38 (F38 n)

/-- The hierarchy along the mixed tree at depth `family38 n`, based on Contender 38's family. -/
def F39 (n : Nat) : Nat := Ordinal.hier family38 (mixTree (family38 n)) (family38 n)

/-- **Contender 39.** Never evaluate it. -/
def contender_39 : Nat := F39 (F39 42)

end BusyLean
