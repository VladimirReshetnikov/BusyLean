# BusyLean Contender 14: Diagonal Hyperreflection

This research package proposes a closed, structurally computable Lean natural
number that is formally proved larger than BusyLean Contender 13.

## Central definition

For each input `n`, the proposal:

1. upgrades dynamic-kind System F-omega reflection to a countable family
   transformer;
2. constructs an input-dependent autonomous W-tree schedule;
3. applies a diagonal hierarchy of transformer lifts of rank
   `family13 n + 1`;
4. defines `F14 n` from that hierarchy and finally
   `contender_14 = F14 (F14 42)`.

The formal development proves:

- `contender_13 < contender_14`;
- pointwise `family13 n < F14 n`;
- every adjacent diagonal rank is strictly increasing;
- the raw dynamic-kind reflection layer is below `F14`;
- every enumerated dynamic-kind program in the current budget is below `F14`.

## Validation

Lean 4.34.0 validation passed on GitHub Actions:

- new definition layer: 0.54 s (15 s budget);
- new proof layer: 0.65 s (60 s budget);
- only `propext` and `Quot.sound` in audited closures;
- 1,918-constant closure avoids all nine earlier contender constants;
- forbidden-construct source scan passed.

See `article/contender14_diagonal_hyperreflection.pdf` for the full argument,
`overlay/` for the Lean sources, `integration/` for application instructions,
and `validation/` for machine-check records.

**Do not evaluate the final contender.**
