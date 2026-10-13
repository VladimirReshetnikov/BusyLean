import BusyLean.Contender8

/-!
# Contender 9: System Fω reflected along the W-language's own trees

Contender 6 reflected the W-language along every tree the W-language defines.
Contender 9 does the same with the much stronger System Fω as the reflected
language. The index trees still come from the W-language: Fω has no
set-theoretic model, so it cannot hand trees back to Lean.

```
stage9 seed .leaf     = reflect9 seed
stage9 seed (.node g) = reflect9 (fun i => stage9 seed (g i))
F9 n          = stage9 (fun _ => family8) index n
contender_9   = F9 (F9 42)
```

`reflect9 fs n` exceeds every visible oracle value `fs i n` (`i ≤ n`) and every
closed Fω program of depth `≤ n`, run with the *unary* oracle
`orc (2^i · (2m+1)) = fs i m`. Fω can compute these codes, so programs reach
any child of a node at any input.

**Do not evaluate `contender_9`.**
-/

namespace BusyLean

/-- The 2-adic valuation of a positive number (`0` for `0`). -/
def v2 (k : Nat) : Nat :=
  if h : k ≠ 0 ∧ k % 2 = 0 then v2 (k / 2) + 1 else 0
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h.1) (by decide)

/-- Decode `k = 2^i · (2m+1)` as `(i, m)`; `0` decodes to `(0, 0)`. -/
def unpair2 (k : Nat) : Nat × Nat :=
  let i := v2 k
  (i, (k / 2 ^ i) / 2)

/-- A family of functions presented to Fω as one unary oracle. -/
def packFamily (fs : W.Family) (k : Nat) : Nat := fs (unpair2 k).1 (unpair2 k).2

/-- One reflection step over System Fω with an oracle family. -/
def reflect9 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fw.fvalue (packFamily fs) n) (Fw.ctmsUpTo n))

/-- Forest reflection of System Fω along a tree of the W-language. -/
def stage9 (seed : W.Family) : BigNumber.WTree Nat → Nat → Nat
  | .leaf => reflect9 seed
  | .node g => reflect9 (fun i => stage9 seed (g i))

/-- Contender 8's construction as a function of its input: `family8 42 = contender_8`. -/
def family8 (n : Nat) : Nat := F8 (F8 n)

/-- Fω forest reflection along the W-language's index, seeded with Contender 8. -/
def F9 (n : Nat) : Nat := stage9 (fun _ => family8) index n

/-- **Contender 9.** Never evaluate it. -/
def contender_9 : Nat := F9 (F9 42)

end BusyLean
