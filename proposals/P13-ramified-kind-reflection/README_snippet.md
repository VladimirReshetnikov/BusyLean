## Proposed Contender 11: diagonal ramified kind-reflection

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)

def F11 (n : Nat) : Nat :=
  RK.ramified (family10 n + 1) (fun _ => family10) n

def contender_11 : Nat := F11 (F11 42)
```

`RK.reflect` is a family-aware reflection step over kind-polymorphic System
Fω.  `RK.autonomous` lifts any family operator along the existing self-indexing
W-tree `index`.  `RK.ramified (r+1)` autonomously lifts the entire rank-`r`
operator, producing a strict hierarchy of reflection operators.  At input 42,
`F11` selects rank `contender_10 + 1`, without mentioning the constant
`contender_10` in the definition.

Proposed formal margins:

| Theorem | Statement |
|---|---|
| `contender_10_lt_contender_11` | required strict comparison |
| `family10_lt_F11` | pointwise domination of the previous construction |
| `RK.ramified_level_lt` | every successor rank strictly exceeds its predecessor |
| `fixed_rank_eventually_lt_F11` | every fixed rank is eventually below the diagonal |
| `fvalue_lt_F11` | all accepted kind-polymorphic programs in the budget are below `F11` |

The definition remains closed and computable, uses no earlier contender
constant, and introduces no `noncomputable`, `partial`, `unsafe`, `opaque`,
`extern`, custom axiom, `sorry`, or `native_decide` declaration.
