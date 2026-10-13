import BusyLean.Contender24

/-!
# Contender 25: reflection-indexed round-tower hyperreflection

```
contender_25 := F25 (F25 42)
F25 n        := wDiagonalLift (schedule25 n) (rank25 n)
                  rStarTransformer (fun _ => family24) n n
```

Contender 24 uses the round-tower ladder `roundTower n` at input `n`.  Here the
round index, syntax depth, and type-checking fuel are no longer the external
input.  They are selected by a full instance of Contender 24's raw reflector:

```
budget25 fs n = n + 1 + reflectRFamily fs n.
```

The new raw reflector therefore ranges over programs on
`roundTower (budget25 fs n)`, at depth and fuel `budget25 fs n`.  With the
constant seed `family24`, the selected round at input 42 is already strictly
larger than Contender 24 itself.  Thus the predecessor's numerical output is
fed back into the ordinal-ladder index, rather than being used only as a finite
rank or schedule height.

The amplifier remains the W-ranked hierarchy of transformer lifts, but both
its schedule and its rank are autonomous hyper-closures whose height is the
self-selected budget.  All recursion is structural or inherited from the
proved well-founded round towers; all finite enumerations have an explicit
natural-number bound.  The construction is executable in principle.

**Do not evaluate `contender_25`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 24's construction as a function of its input:
`family24 42 = contender_24`. -/
def family24 (n : Nat) : Nat := F24 (F24 n)

/-- Reflection-generated round/depth/fuel budget.

It contains a complete `reflectRFamily fs n` computation and then adds a
successor guard.  Consequently it strictly exceeds the old raw reflection,
every visible oracle coordinate, and the external input.
-/
def budget25 (fs : Family) (n : Nat) : Nat :=
  n + 1 + reflectRFamily fs n

/-- Round-tower reflection whose round index, syntax depth, and type-checking
fuel are all chosen by `budget25`.

At every concrete input the search remains finite: `roundLadderUpTo B` is a
finite list, where `B = budget25 fs n`. -/
def reflectRStarFamily (fs : Family) (n : Nat) : Nat :=
  budget25 fs n + 1 +
    BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.rvalue (budget25 fs n) (packFamily fs) (budget25 fs n))
        (FL.roundLadderUpTo (budget25 fs n)))

/-- The reflection-indexed round-tower reflector as a transformer. -/
def rStarTransformer : Transformer := fun fs _ n => reflectRStarFamily fs n

/-- The reflection-generated budget specialized to Contender 24's constant
seed family. -/
def height25 (n : Nat) : Nat := budget25 (fun _ => family24) n

/-- A local schedule placed an autonomous hyper-closure above Contender 24's
schedule, with height controlled by the reflection-generated budget. -/
def schedule25 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height25 n + 42)
      (Autonomous.encode (schedule24 n)))

/-- A W-valued rank placed another autonomous hyper-closure above the new
schedule. -/
def rank25 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height25 n + 42)
      (Autonomous.encode (schedule25 n)))

/-- Reflection-indexed round-tower hyperreflection, seeded with Contender 24's
family. -/
def F25 (n : Nat) : Nat :=
  wDiagonalLift (schedule25 n) (rank25 n)
    rStarTransformer (fun _ => family24) n n

/-- **Contender 25.** Never evaluate it. -/
def contender_25 : Nat := F25 (F25 42)

end BusyLean
