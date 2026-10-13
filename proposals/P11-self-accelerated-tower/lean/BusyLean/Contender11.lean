import BusyLean.Contender10

/-!
# Contender 11: self-accelerated forest reflection

Contender 10 performs one bounded reflection over kind-polymorphic System Fω.
This successor first lifts that reflection to a countable oracle family, then
runs it along the W-language's self-generated index tree. One complete traversal
is a `round11`. The tower repeats complete rounds; at each successor stage the
previous stage is both the oracle seed and the new input.

```
B n          := F10 (F10 n)
T 0          := B
T (k + 1) n  := round11 (T k) (T k n)
F11 n        := T (B n + 1) (B n)
contender_11 := F11 (F11 42)
```

The definition is closed and computable. It uses Contender 10's construction as
`B`, but never mentions the constant `contender_10`.

**Do not evaluate `contender_11`.**
-/

namespace BusyLean

/-- One kind-polymorphic reflection step over a countable oracle family.

The family is packed into the unary oracle already used by Contender 9. Besides
all visible family values, the result exceeds every accepted closed program of
kind-polymorphic System Fω at the current syntax/fuel budget. -/
def reflect11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))

/-- Forest reflection of kind-polymorphic System Fω along a well-founded,
countably branching tree. -/
def stage11 (seed : W.Family) : BigNumber.WTree Nat → Nat → Nat
  | .leaf => reflect11 seed
  | .node g => reflect11 (fun i => stage11 seed (g i))

/-- One complete traversal of the W-language's self-generated index tree,
starting from a unary seed function. -/
def round11 (f : Nat → Nat) (n : Nat) : Nat :=
  stage11 (fun _ => f) index n

/-- Contender 10's construction as a function of its input. In particular,
`family10 42` is definitionally equal to `contender_10`. -/
def family10 (n : Nat) : Nat := F10 (F10 n)

/-- A self-accelerated tower of complete forest-reflection rounds.

At a successor stage, the preceding function is supplied as the oracle seed,
and the round is evaluated at the preceding value. This is deliberately
stronger than merely repeating all rounds at the original input. -/
def tower11 : Nat → Nat → Nat
  | 0 => family10
  | k + 1 => fun n => round11 (tower11 k) (tower11 k n)

/-- The diagonal family: at input `n`, start at `family10 n`, and carry out
`family10 n + 1` self-accelerated complete rounds. -/
def F11 (n : Nat) : Nat :=
  tower11 (family10 n + 1) (family10 n)

/-- **Contender 11.** Never evaluate it. -/
def contender_11 : Nat := F11 (F11 42)

end BusyLean
