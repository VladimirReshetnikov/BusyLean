import BusyLean.Contender30

/-!
# Contender 31: reflection-indexed finite-type closure

```
contender_31 := F31 (F31 42)
F31 n        := wDiagonalLift (schedule31 n) (rank31 n)
                  tlStarTransformer (fun _ => family30) n n
```

Contender 30 uses the address ladder over `Ordinal.typeLevelTree n` at input
`n`, and uses the same external `n` as the maximum finite type level, address
window, program-depth bound, and type-checking fuel.  This contender replaces
all of those controls by a complete instance of Contender 30's raw finite-type
reflector:

```
budget31 fs n = n + 1 + reflectTLFamily fs n.
```

The new raw reflector therefore enumerates programs over addresses in
`typeLevelTree (budget31 fs n)`, at syntax depth and checking fuel
`budget31 fs n`.  With the constant seed `family30`, the selected finite type
level at input 42 already strictly exceeds Contender 30 itself.  Thus the
predecessor's output is fed back into the *type level of the object-language
universe*, not merely into an outer natural iteration or an auxiliary
schedule.

The amplifier remains the W-ranked hierarchy of transformer lifts.  Both its
schedule and its W-valued rank are autonomous hyper-closures above Contender
30's schedule, with height controlled by the same reflection-generated
budget.

All recursion is structural or inherited from the structurally well-founded
address order.  At each concrete input the enumerated program list is finite,
and normalization is performed only for terms carrying a strong-normalization
proof obtained from type checking.  The construction is therefore computable
in principle, although direct evaluation is infeasible.

**Do not evaluate `contender_31`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 30's construction as a function of its input:
`family30 42 = contender_30`. -/
def family30 (n : Nat) : Nat := F30 (F30 n)

/-- Reflection-generated type-level/depth/fuel budget.

It contains a complete `reflectTLFamily fs n` computation and then adds a
successor guard.  Consequently it strictly exceeds the old raw reflection,
every visible oracle coordinate, and the external input.
-/
def budget31 (fs : Family) (n : Nat) : Nat :=
  n + 1 + reflectTLFamily fs n

/-- Finite-type address reflection whose type level, address window, syntax
depth, and type-checking fuel are all chosen by `budget31`.

At every concrete input the search remains finite:
`tltreeLadderUpTo B` is a finite list, where `B = budget31 fs n`. -/
def reflectTLStarFamily (fs : Family) (n : Nat) : Nat :=
  budget31 fs n + 1 +
    BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.tlvalue (budget31 fs n) (packFamily fs) (budget31 fs n))
        (FL.tltreeLadderUpTo (budget31 fs n)))

/-- The reflection-indexed finite-type reflector as a transformer. -/
def tlStarTransformer : Transformer := fun fs _ n => reflectTLStarFamily fs n

/-- The reflection-generated budget specialized to Contender 30's constant
seed family. -/
def height31 (n : Nat) : Nat := budget31 (fun _ => family30) n

/-- A local schedule placed an autonomous hyper-closure above Contender 30's
schedule, with height controlled by the reflection-generated budget. -/
def schedule31 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height31 n + 42)
      (Autonomous.encode (schedule30 n)))

/-- A W-valued rank placed another autonomous hyper-closure above the new
schedule. -/
def rank31 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height31 n + 42)
      (Autonomous.encode (schedule31 n)))

/-- Reflection-indexed finite-type hyperreflection, seeded with Contender 30's
family. -/
def F31 (n : Nat) : Nat :=
  wDiagonalLift (schedule31 n) (rank31 n)
    tlStarTransformer (fun _ => family30) n n

/-- **Contender 31.** Never evaluate it. -/
def contender_31 : Nat := F31 (F31 42)

end BusyLean
