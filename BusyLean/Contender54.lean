import BusyLean.LargeElim

/-!
# Contender 54: the tree-indexed large-elimination diagonal

```
family53 n    := F53 (F53 n)
N             := family53 n
largeTypeTree := lim i =>
  if i = 0 then ramify zero 1
  else ramify (stackTree N) i
F54 n         := largeElim family53 largeTypeTree N
contender_54  := F54 (F54 42)
```

Contender 53 iterates a fixed-output-type reflection along a tree.  Contender 54
changes the resource being diagonalized: the branch tree computes the semantic
type in which iteration takes place.  Branch `i` (for `i > 0`) raises the giant
`stackTree N` through `2*i` successor layers.  The root limit observes every
branch through `i = N`, so the order of the semantic iterator is itself the
already enormous run-time number `N`.

Branch zero is a deliberately transparent comparison witness: it is semantic
order two and reduces definitionally to `iterN family53 N N`.  The nonzero
branches are the novel large-elimination core.

**Do not evaluate `contender_54`.**
-/

namespace BusyLean

open Ordinal (CTree)

/-- Contender 53 as an input-indexed family; `family53 42` is definitionally
`contender_53`. -/
def family53 (n : Nat) : Nat := F53 (F53 n)

/-- The schedule of semantic types used by Contender 54.

The zeroth branch supplies a simple lower-bound witness.  Branch `i > 0`
contains the full Contender-52 stacked tree under `2*i` successor layers, so
`LargeTy` turns it into a type whose order and dependent-product structure are
computed from the preceding contender.
-/
def largeTypeTree (N : Nat) : CTree :=
  .lim fun i =>
    if i = 0 then ramify .zero 1
    else ramify (stackTree N) i

/-- The tree-indexed large-elimination family. -/
def F54 (n : Nat) : Nat :=
  let N := family53 n
  largeElim family53 (largeTypeTree N) N

/-- **Contender 54: Tree-Indexed Large-Elimination Diagonal (TILED).** -/
def contender_54 : Nat := F54 (F54 42)

end BusyLean
