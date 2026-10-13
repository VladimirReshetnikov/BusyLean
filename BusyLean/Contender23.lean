import BusyLean.TreeHyperReflection
import BusyLean.Contender22

/-!
# Contender 23: transfinite-rank hyperreflection over the tower ladders

```
contender_23 := F23 (F23 42)
F23 n        := wDiagonalLift (schedule23 n) (rank23 n) twTransformer (fun _ => family22) n n
```

The language is Contender 22's: at input `n`, the ladder over `Ordinal.tower n`.
The amplifier is upgraded with proposal P22's idea (adopted with attribution
in `TreeHyperReflection`). The rank of the hierarchy of transformer lifts is a
well-founded W-tree instead of a natural number, namely an autonomous notation
above the schedule. Child-rank lifts are spliced and used both to pre-amplify
the base and as the local lift along the schedule.

The seed is Contender 22's family `family22 n = F22 (F22 n)`.

**Do not evaluate `contender_23`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 22's construction as a function of its input: `family22 42 = contender_22`. -/
def family22 (n : Nat) : Nat := F22 (F22 n)

def schedule23 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family22 n + 42) (Autonomous.encode (schedule22 n)))

/-- The transfinite rank: an autonomous notation above the schedule. -/
def rank23 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family22 n + 42) (Autonomous.encode (schedule23 n)))

/-- W-ranked hyperreflection of the tower ladders, seeded with Contender 22's family. -/
def F23 (n : Nat) : Nat :=
  wDiagonalLift (schedule23 n) (rank23 n) twTransformer (fun _ => family22) n n

/-- **Contender 23.** Never evaluate it. -/
def contender_23 : Nat := F23 (F23 42)

end BusyLean
