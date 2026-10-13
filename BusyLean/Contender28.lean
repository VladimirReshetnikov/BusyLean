import BusyLean.Contender27

/-!
# Contender 28: reflection-indexed universe hyperreflection

```
contender_28 := F28 (F28 42)
F28 n        := wDiagonalLift (schedule28 n) (rank28 n)
                  uStarTransformer (fun _ => family27) n n
```

Contender 27 uses the address ladder over `Ordinal.universeLadderTree n` at
input `n`, and uses the same external `n` as the finite address window,
program-depth bound, and type-checking fuel.  This contender replaces all of
those controls by a complete instance of Contender 27's raw universe
reflector:

```
budget28 fs n = n + 1 + reflectUFamily fs n.
```

The new raw reflector therefore enumerates programs over addresses in
`universeLadderTree (budget28 fs n)`, at syntax depth and checking fuel
`budget28 fs n`.  With the constant seed `family27`, the selected universe
index at input 42 already strictly exceeds Contender 27 itself.  Thus the
predecessor's output is fed back into the stratified universe level of the
*object language*, not merely into a finite iteration count or an auxiliary
schedule.

The amplifier remains the W-ranked hierarchy of transformer lifts.  Both its
schedule and its W-valued rank are autonomous hyper-closures above Contender
27's schedule, with height controlled by the same reflection-generated
budget.

All recursion is structural or inherited from the structurally well-founded
address order.  At each concrete input the enumerated program list is finite,
and normalization is performed only for terms carrying a strong-normalization
proof obtained from type checking.  The construction is therefore computable
in principle, although direct evaluation is infeasible.

**Do not evaluate `contender_28`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 27's construction as a function of its input:
`family27 42 = contender_27`. -/
def family27 (n : Nat) : Nat := F27 (F27 n)

/-- Reflection-generated universe/depth/fuel budget.

It contains a complete `reflectUFamily fs n` computation and then adds a
successor guard.  Consequently it strictly exceeds the old raw reflection,
every visible oracle coordinate, and the external input.
-/
def budget28 (fs : Family) (n : Nat) : Nat :=
  n + 1 + reflectUFamily fs n

/-- Universe-address reflection whose universe index, address window, syntax
depth, and type-checking fuel are all chosen by `budget28`.

At every concrete input the search remains finite:
`utreeLadderUpTo B` is a finite list, where `B = budget28 fs n`. -/
def reflectUStarFamily (fs : Family) (n : Nat) : Nat :=
  budget28 fs n + 1 +
    BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.uvalue (budget28 fs n) (packFamily fs) (budget28 fs n))
        (FL.utreeLadderUpTo (budget28 fs n)))

/-- The reflection-indexed universe-address reflector as a transformer. -/
def uStarTransformer : Transformer := fun fs _ n => reflectUStarFamily fs n

/-- The reflection-generated budget specialized to Contender 27's constant
seed family. -/
def height28 (n : Nat) : Nat := budget28 (fun _ => family27) n

/-- A local schedule placed an autonomous hyper-closure above Contender 27's
schedule, with height controlled by the reflection-generated budget. -/
def schedule28 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height28 n + 42)
      (Autonomous.encode (schedule27 n)))

/-- A W-valued rank placed another autonomous hyper-closure above the new
schedule. -/
def rank28 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height28 n + 42)
      (Autonomous.encode (schedule28 n)))

/-- Reflection-indexed universe hyperreflection, seeded with Contender 27's
family. -/
def F28 (n : Nat) : Nat :=
  wDiagonalLift (schedule28 n) (rank28 n)
    uStarTransformer (fun _ => family27) n n

/-- **Contender 28.** Never evaluate it. -/
def contender_28 : Nat := F28 (F28 42)

end BusyLean
