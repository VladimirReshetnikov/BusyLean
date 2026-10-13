## Current contender: Contender 20

```lean
def family19 (n : Nat) : Nat := F19 (F19 n)                 -- Contender 19 = family19 42
def baseLift20 (n : Nat) : TransformerLift :=
  diagonalLift (schedule20 n) (family19 n + 1)
def F20 (n : Nat) : Nat :=
  diagonalHyperLift (schedule20 n) (family19 n + 1)
    (baseLift20 n) lTransformer (fun _ => family19) n n
def contender_20 : Nat := F20 (F20 42)

theorem contender_19_lt_contender_20 : contender_19 < contender_20
```

Contender 19 diagonalizes transformer lifts. Contender 20 raises the amplifier
one type level: a `HyperLift` maps whole transformer lifts to transformer lifts.
`diagonalHyperLift` repeats the same diagonal pattern at this new level, using
the preceding hyper-rank both as the local operator over a W-tree schedule and
as the first amplification of the base lift.

At every input, the proof exhibits a strict two-step chain:

```lean
family19 n < firstOrder20 n < F20 n
```

Here `firstOrder20 n` is already a complete first-order `diagonalLift` layer,
with schedule and rank controlled by `family19 n`. The second inequality is not
oracle monotonicity; it follows from explicit occurrences of the base lift and
child zero in the second-order splice. All definitions are structural and
computable.

| Theorem | Statement |
|---|---|
| `diagonalHyperLift_preservesGoodLifts` | every second-order rank preserves progressive, strictly inflationary lifts |
| `diagonalHyperLift_strictlyLiftInflationary` | every second-order rank strictly exceeds its base lift |
| `family19_lt_firstOrder20` | the complete Contender 19 family is below the embedded first-order layer |
| `firstOrder20_lt_F20` | the embedded first-order layer is below the second-order result |
| `contender_19_lt_contender_20` | Contender 19 < Contender 20 |
