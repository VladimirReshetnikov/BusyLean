import BusyLean.TreeHyperReflectionFacts
import BusyLean.Contender19

/-!
# Contender 20: W-ranked hyperreflection over the large-Veblen ladder

Contender 19 uses the finite rank hierarchy `diagonalLift schedule k`, with a
rank `k` selected from Contender 18's family.  Here the hierarchy itself is
indexed by an arbitrary well-founded `WTree Nat`.

For input `n` we first turn Contender 19's construction into an oracle family

```
family19 n = F19 (F19 n).
```

We then build two autonomous trees above Contender 19's schedule.  The first is
the local schedule traversed at every rank node.  The second is the rank tree
of the new hierarchy.  Finally `wDiagonalLift` recursively splices all child
ranks, pre-amplifies its base with that splice, and traverses the schedule using
the same lower-rank lift.

All definitions are closed and computable.  **Do not evaluate `contender_20`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 19's construction as a function of its input:
`family19 42 = contender_19`. -/
def family19 (n : Nat) : Nat := F19 (F19 n)

/-- A local operator schedule placed autonomously above Contender 19's own
schedule, with a self-fed number of higher derivatives. -/
def schedule20 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family19 n + 42)
      (Autonomous.encode (schedule19 n)))

/-- The W-valued rank of the lift hierarchy.  It is placed another autonomous
closure above the local schedule rather than collapsed to a natural rank. -/
def rank20 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family19 n + 42)
      (Autonomous.encode (schedule20 n)))

/-- W-ranked hyperreflection of the large-Veblen ladder, seeded with Contender
19's family. -/
def F20 (n : Nat) : Nat :=
  wDiagonalLift (schedule20 n) (rank20 n)
    lTransformer (fun _ => family19) n n

/-- **Contender 20.** Never evaluate it. -/
def contender_20 : Nat := F20 (F20 42)

end BusyLean
