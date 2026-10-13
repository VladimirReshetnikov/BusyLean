import BusyLean.Contender6

/-!
# Contender 7: seeded reflection power

The current `stage` scheduler performs forest reflection through a `WTree Nat`.
`liftStage` promotes an arbitrary scheduler `S` by using a second W-tree as an
operator-level control object.  A leaf runs `S` through the universal `index`;
a node feeds the promoted values of all children back to `S` as its oracle
family, again at `index`.

`stageOrder k` iterates this promotion `k` times.  The final height is the P5
seed value at 42, plus a fixed positive guard.  The definition does not use the
value `BusyLean.contender_6` as an iteration counter.

Do not evaluate `contender_7`.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- A forest-reflection scheduler: oracle family, control tree, input. -/
abbrev StageOperator := Family → WTree Nat → Nat → Nat

/-- Raise a scheduler by one reflection order.

At a leaf, run `S` with the supplied seed through the universal index.  At a
node, recursively promote every child and expose the resulting family to `S`.
All recursion is structural recursion on the W-tree. -/
def liftStage (S : StageOperator) (seed : Family) : WTree Nat → Nat → Nat
  | .leaf => S seed index
  | .node f => S (fun i => liftStage S seed (f i)) index

/-- The finite hierarchy of scheduler orders. -/
def stageOrder : Nat → StageOperator
  | 0 => stage
  | k + 1 => liftStage (stageOrder k)

/-- A large, closed, computable promotion height.

The successor guard makes positivity definitional, so the comparison proof
never needs to normalize the P5 value. -/
def metaHeight : Nat := Nat.succ (42 + p5Family 0 42)

/-- **Contender 7.**  Never evaluate it. -/
def contender_7 : Nat := stageOrder metaHeight p5Family index 42

end BusyLean
