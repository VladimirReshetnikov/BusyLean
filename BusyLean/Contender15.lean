import BusyLean.HyperReflection
import BusyLean.Autonomous
import BusyLean.Contender12
import BusyLean.Contender14

/-!
# Contender 15: diagonal hyperreflection over the ladder

```
contender_15 := F15 (F15 42)
F15 n        := diagonalLift (schedule15 n) (rank15 n) flFamilyTransformer (fun _ => family14) n n
```

The strongest language in the repository (Contender 14's ladder of universes)
meets the strongest amplifier received (proposal P17's rank hierarchy of
transformer lifts, found independently in P20).

* `reflectFLFamily fs n` exceeds every visible coordinate `fs i n` (`i ≤ n`)
  and the value of every level-`n` ladder program of depth `≤ n`. The
  programs get the whole family through the packed oracle
  `packFamily fs`.
* `diagonalLift schedule k` is a hierarchy of transformer lifts. Rank 0 is the
  autonomous lift; rank `k+1` traverses `schedule` using rank `k` as the lift
  at every node, after pre-amplifying the base with rank `k`.
* The schedule stacks `family14 n + 42` hyper-closures above Contender 12's
  `tree12`, and the rank is `family14 n + 1`.

The seed is Contender 14's family `family14 n = F14 (F14 n)`.

**Do not evaluate `contender_15`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Ladder reflection with a countable oracle family; the visible prefix
maximum makes the transformer progressive without any monotonicity. -/
def reflectFLFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.fvalue n (packFamily fs) n) (FL.ladderUpTo n))

/-- Family ladder reflection as a transformer (all output coordinates agree). -/
def flFamilyTransformer : Transformer :=
  fun fs _ n => reflectFLFamily fs n

/-- Contender 14's construction as a function of its input: `family14 42 = contender_14`. -/
def family14 (n : Nat) : Nat := F14 (F14 n)

/-- The input-dependent autonomous schedule above `tree12`. -/
def schedule15 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family14 n + 42) (Autonomous.encode tree12))

/-- The diagonal rank. -/
def rank15 (n : Nat) : Nat := family14 n + 1

/-- Diagonal hyperreflection of the ladder, seeded with Contender 14's family. -/
def F15 (n : Nat) : Nat :=
  diagonalLift (schedule15 n) (rank15 n) flFamilyTransformer (fun _ => family14) n n

/-- **Contender 15.** Never evaluate it. -/
def contender_15 : Nat := F15 (F15 42)

end BusyLean
