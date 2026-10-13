import BusyLean.Contender25

/-!
# Contender 26: reflection-indexed tree-collapse hyperreflection

```
contender_26 := F26 (F26 42)
F26 n        := wDiagonalLift (schedule26 n) (rank26 n)
                  aStarTransformer (fun _ => family25) n n
```

Contender 25 uses the address ladder over `Ordinal.bigTree n` at input `n`,
and it also uses `n` as the syntax-depth and type-checking-fuel bound.  This
contender replaces all three external bounds by a complete instance of
Contender 25's raw address reflector:

```
budget26 fs n = n + 1 + reflectAFamily fs n.
```

The new raw reflector therefore enumerates programs over addresses in
`bigTree (budget26 fs n)`, at syntax depth and checking fuel
`budget26 fs n`.  With the constant seed `family25`, the selected tree index at
input 42 already strictly exceeds Contender 25 itself.  In particular, the
predecessor's numerical output is fed back into the *object-language ordinal
index*, not merely into a finite iteration count or an auxiliary schedule.

The amplifier remains the W-ranked hierarchy of transformer lifts.  Both its
schedule and its W-valued rank are placed autonomous hyper-closures above
Contender 25's schedule, with closure height controlled by the same
reflection-generated budget.

All recursion is structural or inherited from the structurally well-founded
address order.  At every concrete input the enumerated program list is finite
and every normalization computation has an explicit fuel/type derivation.
Thus the number is executable in principle, although direct evaluation is
infeasible.

**Do not evaluate `contender_26`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 25's construction as a function of its input:
`family25 42 = contender_25`. -/
def family25 (n : Nat) : Nat := F25 (F25 n)

/-- Reflection-generated tree/depth/fuel budget.

It contains a complete `reflectAFamily fs n` computation and then adds a
successor guard.  Consequently it strictly exceeds the old raw reflection,
every visible oracle coordinate, and the external input.
-/
def budget26 (fs : Family) (n : Nat) : Nat :=
  n + 1 + reflectAFamily fs n

/-- Address-ladder reflection whose tree index, syntax depth, and type-checking
fuel are all chosen by `budget26`.

At every concrete input the search remains finite:
`addrLadderUpTo B` is a finite list, where `B = budget26 fs n`. -/
def reflectAStarFamily (fs : Family) (n : Nat) : Nat :=
  budget26 fs n + 1 +
    BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.avalue (budget26 fs n) (packFamily fs) (budget26 fs n))
        (FL.addrLadderUpTo (budget26 fs n)))

/-- The reflection-indexed address-ladder reflector as a transformer. -/
def aStarTransformer : Transformer := fun fs _ n => reflectAStarFamily fs n

/-- The reflection-generated budget specialized to Contender 25's constant
seed family. -/
def height26 (n : Nat) : Nat := budget26 (fun _ => family25) n

/-- A local schedule placed an autonomous hyper-closure above Contender 25's
schedule, with height controlled by the reflection-generated budget. -/
def schedule26 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height26 n + 42)
      (Autonomous.encode (schedule25 n)))

/-- A W-valued rank placed another autonomous hyper-closure above the new
schedule. -/
def rank26 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height26 n + 42)
      (Autonomous.encode (schedule26 n)))

/-- Reflection-indexed tree-collapse hyperreflection, seeded with Contender
25's family. -/
def F26 (n : Nat) : Nat :=
  wDiagonalLift (schedule26 n) (rank26 n)
    aStarTransformer (fun _ => family25) n n

/-- **Contender 26.** Never evaluate it. -/
def contender_26 : Nat := F26 (F26 42)

end BusyLean
