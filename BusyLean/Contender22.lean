import BusyLean.TreeHyperReflectionFacts
import BusyLean.Contender21

/-!
# Contender 22: self-budgeted W-ranked Buchholz hyperreflection

Contender 21 uses Buchholz ladders with external level and syntax budget `n`,
and a finite natural-number rank for diagonal hyperreflection.  This contender
strengthens both axes.

First, the base reflector computes a *self budget*

```
budget22 fs n = n + 1 + prefixMax (fun i => fs i n) n.
```

It then enumerates Buchholz atoms through level `budget22 fs n`, enumerates
ladder programs through the same depth, type-checks them with the same fuel,
and dominates all accepted values.  With the constant seed `family21`, the
budget at input 42 is already strictly larger than Contender 21 itself.

Second, the finite rank `diagonalLift schedule k` is replaced by
`wDiagonalLift schedule rank`, whose rank is an arbitrary well-founded
`WTree Nat`.  Both the local schedule and the rank tree are placed autonomous
hyper-closures above Contender 21's schedule, with a height selected from the
self budget.

All recursion is structural or well-founded, all enumerations are finite, and
the construction is executable in principle.  **Do not evaluate
`contender_22`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 21's construction as a function of its input:
`family21 42 = contender_21`. -/
def family21 (n : Nat) : Nat := F21 (F21 n)

/-- The finite level/depth/fuel budget used by the new Buchholz reflector.
It strictly exceeds every visible seed coordinate. -/
def budget22 (fs : Family) (n : Nat) : Nat :=
  n + 1 + prefixMax (fun i => fs i n) n

/-- Self-budgeted Buchholz-ladder reflection.

Unlike `reflectZFamily`, whose level and program budget are the external input
`n`, this reflector uses `budget22 fs n`.  Thus its finite search boundary is
itself driven above the visible oracle envelope. -/
def reflectZStarFamily (fs : Family) (n : Nat) : Nat :=
  budget22 fs n + 1 +
    BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum
        (FL.zvalue (budget22 fs n) (packFamily fs) (budget22 fs n))
        (FL.buchholzLadderUpTo (budget22 fs n)))

/-- The self-budgeted Buchholz reflector as a transformer. -/
def zStarTransformer : Transformer := fun fs _ n => reflectZStarFamily fs n

/-- The self budget specialized to Contender 21's constant seed family. -/
def height22 (n : Nat) : Nat := budget22 (fun _ => family21) n

/-- A local W-schedule autonomously above Contender 21's schedule. -/
def schedule22 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height22 n + 42)
      (Autonomous.encode (schedule21 n)))

/-- A W-valued rank placed another autonomous closure above the local schedule. -/
def rank22 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (height22 n + 42)
      (Autonomous.encode (schedule22 n)))

/-- Self-budgeted W-ranked Buchholz hyperreflection, seeded with Contender 21's
family. -/
def F22 (n : Nat) : Nat :=
  wDiagonalLift (schedule22 n) (rank22 n)
    zStarTransformer (fun _ => family21) n n

/-- **Contender 22.** Never evaluate it. -/
def contender_22 : Nat := F22 (F22 42)

end BusyLean
