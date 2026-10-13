import BusyLean.TransfiniteHyperReflection
import BusyLean.Contender19

/-!
# Contender 20: W-rank hyperreflection

```
family19 n      := F19 (F19 n)
seedLift20 n    := diagonalLift (schedule20 n) (family19 n + 1)
lift20 n        := treeDiagonalLift (schedule20 n) (rankTree20 n) (seedLift20 n)
F20 n           := lift20 n lTransformer seedFamily20 n n
contender_20     := F20 (F20 42)
```

Contender 19 uses a natural-number rank of transformer lifts.  Contender 20
raises the rank mechanism one type level and iterates it along a countably
branching well-founded tree.  At an outer node, the recursively generated child
lifts are spliced into a single lift, then one diagonal rank step is applied.

The seed is already a diagonal lift of rank `family19 n + 1`.  The outer rank
tree is an autonomous hyperclosure above a schedule that is itself an
autonomous hyperclosure above Contender 19's schedule.  The object-language
transformer remains the large-Veblen-ladder reflector.

Do not evaluate `contender_20`.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 19's construction as a function of its input. -/
def family19 (n : Nat) : Nat := F19 (F19 n)

/-- The constant oracle family used by Contender 20. -/
def seedFamily20 : Family := fun _ => family19

/-- Inner schedule: a self-height autonomous closure above Contender 19's
schedule. -/
def schedule20 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family19 n + 42) (Autonomous.encode (schedule19 n)))

/-- Outer W-rank: another self-height autonomous closure, now above the inner
schedule itself. -/
def rankTree20 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family19 n + 42) (Autonomous.encode (schedule20 n)))

/-- The finite-rank lift from which the W-rank closure starts. -/
def seedLift20 (n : Nat) : TransformerLift :=
  diagonalLift (schedule20 n) (family19 n + 1)

/-- The W-rank lift used at input `n`. -/
def lift20 (n : Nat) : TransformerLift :=
  treeDiagonalLift (schedule20 n) (rankTree20 n) (seedLift20 n)

/-- Pointwise Contender-20 family. -/
def F20 (n : Nat) : Nat :=
  lift20 n lTransformer seedFamily20 n n

/-- Contender 20.  Never evaluate it. -/
def contender_20 : Nat := F20 (F20 42)

end BusyLean
