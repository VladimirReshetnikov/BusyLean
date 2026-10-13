# Claim-status matrix

| Claim | Status in this package | Authoritative next check |
|---|---|---|
| The definition is closed and computable in principle | Established from structurally recursive source and inherited total evaluators | Lean elaboration and audit |
| No earlier contender constant occurs in the executable definition source | Static audit: PASS | Lean transitive closure audit |
| `family10_lt_F11` | Complete paper proof and proposed Lean proof | Kernel compilation |
| `RK.ramified_level_lt` | Complete paper proof and proposed Lean proof | Kernel compilation |
| `fixed_rank_eventually_lt_F11` | Complete paper proof and proposed Lean proof | Kernel compilation |
| `contender_10_lt_contender_11` | Complete paper proof and proposed Lean proof | Kernel compilation |
| Only permitted axioms are used | Expected from dependencies and proof terms; not measured here | `#print axioms` in Lean 4.34.0 |
| Definition/proof time budgets are met | Not measured | Clean build with supplied harness |
| Finite surrogate recurrence behaves as intended | Python tests: PASS | Not a substitute for Lean |
| PDF is compiled, rendered, and visually sound | PASS | None |
| Named proof-theoretic ordinal for DRKR | Not claimed; article gives only a labeled heuristic | Future ordinal analysis |
