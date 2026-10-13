# Formal claims supplied by `Comparison14.lean`

The intended kernel-checked claims are:

1. `oracle_lt_reflect14`: every visible family coordinate is below one new
   family-aware dynamic-kind reflection step.
2. `fvalue_lt_reflect14`: every accepted dynamic-kind System F-omega program
   at the current budget is below that step.
3. `fdTransformer_progressive`: the new base transformer satisfies the exact
   generic hypothesis required by BusyLean's operator machinery.
4. `operatorPower_progressive`: every finite iteration of the complete
   operator stage remains progressive.
5. `operatorPower_step_lt`: successive powers form a strict chain at visible
   coordinates.
6. `family13_twice_lt_F14`: the previous family evaluated at its own value is
   below the new family at every input.
7. `family13_lt_F14`: the entire Contender 13 family is pointwise below `F14`.
8. `fvalue_lt_F14`: the new family also dominates every accepted Fd program at
   the diagonal budget used by the construction.
9. `contender_13_lt_contender_14`: the required strict comparison.

No asymptotic or proof-theoretic-ordinal estimate in the article is claimed as
formal. Those estimates are explicitly labeled heuristic.
