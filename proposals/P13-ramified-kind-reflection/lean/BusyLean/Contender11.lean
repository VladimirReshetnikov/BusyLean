import BusyLean.Contender10

/-!
# Contender 11: diagonal ramified kind-reflection

This module contains only the computable definitions.  The comparison and
structural theorems are in `BusyLean/Comparison11.lean`.

The construction has three layers.

1. `RK.reflect` is a family-aware version of Contender 10's reflection over
   kind-polymorphic System Fω.  The unary object-language oracle decodes a
   pair `(i,m)` and calls the family member `fs i m`.
2. `RK.autonomous` lifts any family operator along Contender 6's self-indexing
   W-tree `index`, which joins every tree definable in the W-language.
3. `RK.ramified r` iterates the autonomous lift at the meta-level.  The rank
   used at input `n` is `family10 n + 1`, already larger than `n`; the current
   accepted construction is also used as the seed family.

No earlier contender *constant* occurs in the definition.  In particular,
`contender_10` is not referenced.  Only its construction `F10` is reused.
Every definition below is structurally recursive and executable in principle.

**Never evaluate `contender_11`.**
-/

namespace BusyLean

namespace RK

/-- A transformation from an oracle family to a numerical function. -/
abbrev Operator := W.Family → Nat → Nat

/-- One family-aware reflection step over kind-polymorphic System Fω.

The first maximum sees all oracle-family values `fs i n` with `i ≤ n`.
The second sees all accepted object-language programs of syntax depth `≤ n`,
run with the packed unary oracle.  The additive guard makes the result also
strictly exceed the input. -/
def reflect (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN
    (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))

/-- Lift a family operator through a W-tree.

At a leaf, apply the operator to the seed family.  At a node, expose the
values obtained from every child as the new family seen by the operator. -/
def lift (op : Operator) (seed : W.Family) :
    BigNumber.WTree Nat → Nat → Nat
  | .leaf => op seed
  | .node g => op (fun i => lift op seed (g i))

/-- Autonomous lifting along the join of every W-tree definable by the
repository's W-language. -/
def autonomous (op : Operator) (seed : W.Family) : Nat → Nat :=
  lift op seed index

/-- Ramified autonomous kind-reflection.

Rank zero is one family-aware kind-polymorphic reflection.  A successor rank
lifts the entire previous-rank operator along the self-indexing W-tree.  Thus
rank two is not merely two calls to `reflect`: each outer node invokes a full
rank-one autonomous hierarchy on its family of children. -/
def ramified : Nat → Operator
  | 0 => reflect
  | r + 1 => autonomous (ramified r)

end RK

/-- Contender 10's construction as a function of its input.

Definitional equality gives `family10 42 = contender_10`, but the constant
`contender_10` itself is absent from this module's dependency closure. -/
def family10 (n : Nat) : Nat := F10 (F10 n)

/-- The diagonal ramified family.

At input `n`, the ramification rank is `family10 n + 1`, and the constant
family with value `family10` is the seed. -/
def F11 (n : Nat) : Nat :=
  RK.ramified (family10 n + 1) (fun _ => family10) n

/-- **Contender 11.** Never evaluate it. -/
def contender_11 : Nat := F11 (F11 42)

end BusyLean
