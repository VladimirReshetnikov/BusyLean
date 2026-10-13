# Design summary: Ramified Dynamic Operator Reflection

## 1. Why this is a qualitative extension

The current BusyLean champion, Contender 13, applies a unary dynamic-kind
System Fω reflector to the family representing Contender 12 and then performs
the usual outer self-application.  Merely writing `Ackermann contender_13`, a
large exponent tower, or any other arithmetic wrapper would violate the
contest's no-laziness principle and would provide no construction-level
advance.

RDOR instead changes the reflection architecture in three linked ways.

1. **Family-aware dynamic reflection.** `reflectFdFamily` grants each accepted
   dynamic-kind program a packed oracle encoding a countable family.  Its
   finite maximum explicitly includes every family coordinate visible at the
   current budget.
2. **Strict transformer feedback.** `towerStep base` first computes the whole
   output family `base seed`, then uses that family as the seed of
   `operatorStage base tree14`.  Progressivity makes this a strict pointwise
   increase without any monotonicity assumption on program behavior.
3. **Input-indexed ramification.** `operatorTower (n+1)` repeats the entire
   feedback closure `n+1` times.  This is a tower of transformer closures, not
   a numerical loop applied after the old contender has been named.

The seed `seed13 i n = iterateF13 i (family13 n)` makes all finite additional
iterations of the Contender-13 construction available as family coordinates.
At the contest input, coordinate 42 gives a concrete, interpretation-free
margin: forty-two additional `F13` reflections starting from Contender 13 are
already below `F14 42`.

## 2. The central invariant

A transformer `op : Family → Family` is **progressive** when

```text
seed i n < op seed o n   whenever i ≤ n.
```

This invariant is deliberately weaker than monotonicity.  Reflection
interpreters may inspect oracle values and branch on them, so monotonicity in
the oracle is generally unavailable.  Every proof instead follows an explicit
occurrence in a finite prefix maximum or in the tree/operator-stage structure.

The proof architecture is:

```text
reflectFdFamily finite maximum
        ⇒ fdFamilyTransformer progressive
        ⇒ operatorStage base tree14 progressive
        ⇒ base seed < towerStep base seed
        ⇒ towerStep base progressive
        ⇒ every operatorTower level progressive
        ⇒ seed13 i n < F14 n for i ≤ n.
```

The main comparison is then short:

```text
contender_13 = family13 42 < F14 42
F14 42 < F14 (F14 42) = contender_14
```

## 3. The schedule

Contender 12 uses

```lean
tree12 = Autonomous.realize
  (Autonomous.hyper 42 (Autonomous.encode index))
```

above the W-language's self-generated index.  RDOR stacks the same transparent
closure once more:

```lean
tree14 = Autonomous.realize
  (Autonomous.hyper 42 (Autonomous.encode tree12))
```

No quotient-level ordinal identity is needed.  `tree14` is an executable,
well-founded schedule, and all formal inequalities follow from structural
progressivity.  Any fast-growing or proof-theoretic interpretation is therefore
heuristic context, not a premise of the proof.

## 4. Computability and admissibility

The final term is a closed `Nat`.  It is computable in principle because:

- all syntax enumerations are finite lists bounded by a natural input;
- the dynamic-kind evaluator uses the repository's total normalization proof;
- all W-tree and operator-tower recursion is structural;
- finite maxima are computed by existing total functions;
- the new source uses no oracle, unbounded minimization, partial definition,
  unsafe code, foreign implementation, or noncomputable choice.

As in earlier BusyLean contenders, evaluating the number is infeasible and is
not required.  Kernel checking unfolds only enough definitions to verify types
and proofs; it must never attempt to normalize the numeral itself.

## 5. What is rigorous and what remains heuristic

Encoded rigorously in Lean source:

- structural computability of the definitions;
- visible-family and bounded-program strict inequalities;
- progressivity preservation;
- strict transformer-level and tower-level growth;
- the predecessor comparison and explicit 42-step margin.

Not claimed as a theorem:

- an exact proof-theoretic ordinal for dynamic-kind System Fω;
- an exact fast-growing-hierarchy index for `operatorTower`;
- a comparison with hypothetical future dynamic-kind ladders or CIC-style
  large-elimination languages.

The article labels such interpretations as heuristic and bases every contest
claim on explicit Lean inequalities instead.
