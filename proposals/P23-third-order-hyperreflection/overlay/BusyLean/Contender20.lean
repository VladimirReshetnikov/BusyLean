import BusyLean.SuperReflection
import BusyLean.Contender19

/-!
# Contender 20: third-order autonomous hyperreflection

The preceding construction already forms a hierarchy of transformer lifts.
This contender reflects over those lifts themselves.

At input `n`:

1. `family19 n = F19 (F19 n)` supplies the preceding construction as a seed;
2. `schedule20 n` is an autonomous W-tree with `family19 n + 42` higher
   closures above `tree12`;
3. an ordinary `diagonalLift` of rank `family19 n + 1` is the initial lift;
4. `superIterate` applies a third-order autonomous closure
   `family19 n + 1` times to that entire lift;
5. the resulting lift acts on large-Veblen reflection and yields a countable
   family;
6. one final large-Veblen reflection sees that whole family.

All recursion is structural and the definition is a closed computable `Nat`.
Never evaluate `contender_20`.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 19's construction as a function of its input. -/
def family19 (n : Nat) : Nat := F19 (F19 n)

/-- Contender 19's construction repeated at every seed coordinate. -/
def seed19 : Family := fun _ => family19

/-- A previous-number-controlled autonomous schedule. -/
def schedule20 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family19 n + 42) (Autonomous.encode tree12))

/-- Rank of the initial, current-style diagonal lift. -/
def innerRank20 (n : Nat) : Nat := family19 n + 1

/-- Rank of the new third-order iteration. -/
def metaRank20 (n : Nat) : Nat := family19 n + 1

/-- The third-order lift used at input `n`. -/
def lift20 (n : Nat) : TransformerLift :=
  superIterate (schedule20 n) (metaRank20 n)
    (diagonalLift (schedule20 n) (innerRank20 n))

/-- The complete family produced by the third-order lift. -/
def hyperFamily20 (n : Nat) : Family :=
  lift20 n lTransformer seed19

/-- One final large-Veblen reflection over the complete third-order family. -/
def F20 (n : Nat) : Nat :=
  reflectLFamily (hyperFamily20 n) n

/-- Contender 20.  Never evaluate it. -/
def contender_20 : Nat := F20 (F20 42)

end BusyLean
