# Proposed formal claims

These declarations are contained in the overlay and are included in the focused
axiom audit. They are source-complete but require Lean 4.34.0 kernel replay.

```lean
-- Generic meta-rank separation
theorem rankLift_step_lt (schedule : WTree Nat) (r : Nat)
    {base : Transformer} (hbase : Progressive base) (seed : Family)
    {o n : Nat} :
    rankLift schedule r base seed 0 n <
      rankLift schedule (r + 1) base seed o n

-- Pointwise comparison with the full Contender 13 family
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n

-- Required contest comparison
theorem contender_13_lt_contender_14 : contender_13 < contender_14

-- Escape from every fixed finite meta-rank
theorem fixed_rank_lt_diagonalRank14 {k n : Nat} (hkn : k ≤ n) :
    k < diagonalRank14 n

-- Final dynamic-kind program domination
theorem fvalue_lt_F14 {n : Nat} {t : Fd.CTm}
    (ht : t ∈ Fd.ctmsUpTo n) :
    Fd.fvalue (packFamily (rankFamily14 n)) n t < F14 n
```

The core comparison chain is

```text
family13 n
  < rankFamily14 n 0 n     (generic progressivity of rankLift)
  < F14 n                  (visible-family-coordinate bound)
```

and the outer diagonal is

```text
contender_13 = family13 42
             < F14 42
             < F14 (F14 42)
             = contender_14.
```
