# Recorded Lean verification receipt

## Target

- BusyLean snapshot: `4c4b03d0e2003c479e3bee90a21c8bea13f66c40`
- Lean environment: `lean-4.34.0`
- Proposal: Contender 11, self-indexed forest reflection of kind-polymorphic
  System F-omega

## Results

The exact dependency closure of `BusyLean.Comparison10` contains 30 modules.
It was reconstructed in topological order, with module imports removed, and
checked as one source unit before adding the proposal:

- `okay = true`
- `failed_declarations = []`
- total request time: 8,513 ms

The same dependency unit plus `BusyLean/Contender11.lean`,
`BusyLean/Comparison11.lean`, theorem checks, and axiom reports returned:

- `okay = true`
- `failed_declarations = []`
- total request time: 8,900 ms
- accepted theorem:
  `BusyLean.contender_10_lt_contender_11 : contender_10 < contender_11`
- accepted final program bound: `BusyLean.fvalue_lt_contender_11`

Lean reported exactly `[propext, Quot.sound]` for each of:

1. `BusyLean.contender_11`
2. `BusyLean.contender_10_lt_contender_11`
3. `BusyLean.family10_lt_F11`
4. `BusyLean.defined_tree_eventually_lt11`
5. `BusyLean.fvalue_lt_contender_11`

A separate transitive dependency audit returned:

```text
BusyLean.contender_11: closure of 1460 constants avoids all 8 forbidden names
```

The forbidden set contained `BusyLean.contender_5` through
`BusyLean.contender_10`, plus `BigNumber.contender_5` and
`BigNumber.contender_6`.

## Exact local source hashes

```text
61de7940c3c4cda4ee9c3ee45d40f185eec43097911784112f5f4e9e92cd0dc6  BusyLean/Contender11.lean
e68893844e6ca6e9f589357839a1e44c40705fefdd80d7ec52a55fbd368f3166  BusyLean/Comparison11.lean
```

## Scope and caveat

This is a strong elaborator/kernel check of a reconstructed merged source unit.
AXLE supplies its standard header, so it is not byte-for-byte the same build
route as BusyLean's Lake project.  It does **not** certify the contest timing
budgets on a target machine.  The archive therefore also supplies
`scripts/check_contender11.py`, which performs the required staged clean Lake
build and standalone audit after integration.

The reproducibility script `scripts/verify_axle.py` pins the repository snapshot,
reconstructs the dependency graph, appends the exact local modules, repeats the
axiom and predecessor-closure audits, and saves the returned JSON.
