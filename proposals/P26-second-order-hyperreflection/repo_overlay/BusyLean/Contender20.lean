import BusyLean.SecondOrderReflection
import BusyLean.Contender19

/-!
# Contender 20: second-order diagonal hyperreflection

```
family19 n    := F19 (F19 n)
schedule20 n  := hyper (family19 n + 42) above schedule19 n
rank20 n      := family19 n + 1
baseLift20 n  := diagonalLift (schedule20 n) (rank20 n)
firstOrder20 n := baseLift20 n lTransformer (fun _ => family19) n n
F20 n         := diagonalHyperLift (schedule20 n) (rank20 n)
                   (baseLift20 n) lTransformer (fun _ => family19) n n
contender_20  := F20 (F20 42)
```

Contender 19 diagonalizes a hierarchy of transformer lifts. Contender 20 makes
the next type-level jump: it diagonalizes hyperlifts, which act on complete
transformer-lift hierarchies. At each input, the construction first builds a
full first-order diagonal layer of predecessor-sized rank, then places that
layer inside a second-order diagonal hierarchy of the same predecessor-sized
rank. The schedule is an `Autonomous.hyper` closure constructed from
Contender 19's own schedule syntax.

**Do not evaluate `contender_20`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 19 as a family: `family19 42 = contender_19`. -/
def family19 (n : Nat) : Nat := F19 (F19 n)

/-- A predecessor-sized autonomous hyper-closure constructed from
Contender 19's schedule syntax. No semantic tree ordering is needed. -/
def schedule20 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family19 n + 42) (Autonomous.encode (schedule19 n)))

/-- Both reflection orders are indexed by a number exceeding the complete
predecessor family at the same input. -/
def rank20 (n : Nat) : Nat := family19 n + 1

/-- The first-order diagonal lift embedded as the base of the new hierarchy. -/
def baseLift20 (n : Nat) : TransformerLift :=
  diagonalLift (schedule20 n) (rank20 n)

/-- The complete first-order layer contained inside `F20 n`. -/
def firstOrder20 (n : Nat) : Nat :=
  baseLift20 n lTransformer (fun _ => family19) n n

/-- Second-order diagonal hyperreflection, seeded with Contender 19's family. -/
def F20 (n : Nat) : Nat :=
  diagonalHyperLift (schedule20 n) (rank20 n)
    (baseLift20 n) lTransformer (fun _ => family19) n n

/-- **Contender 20.** Never evaluate it. -/
def contender_20 : Nat := F20 (F20 42)

end BusyLean
