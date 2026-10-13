## Current contender: Contender 11

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)

def round11 (f : Nat → Nat) (n : Nat) : Nat :=
  stage11 (fun _ => f) index n

def tower11 : Nat → Nat → Nat
  | 0 => family10
  | k + 1 => fun n => round11 (tower11 k) (tower11 k n)

def F11 (n : Nat) : Nat :=
  tower11 (family10 n + 1) (family10 n)

def contender_11 : Nat := F11 (F11 42)

theorem contender_10_lt_contender_11 : contender_10 < contender_11
```

A `round11` reflects kind-polymorphic System Fω at every node of `index`, the
join of every W-tree denoted by the repository's W-language. The tower repeats
whole rounds. Its successor uses the preceding stage as the oracle seed and
runs the round at the preceding stage's own value. Finally, `F11 n` carries out
`family10 n + 1` such rounds at input `family10 n`.

The comparison uses explicit inclusion rather than oracle monotonicity:

- each reflection step exceeds every visible child and accepted program;
- a full round contains the constant seed through the path leaf ->
  `treesOfDepth 0` -> `index`;
- every tower successor strictly exceeds the preceding stage; and
- `family10 42` is definitionally Contender 10.

| Theorem | Statement |
|---|---|
| `contender_10_lt_contender_11` | Contender 10 < Contender 11 |
| `family10_lt_F11` | Contender 10's family is beaten at every input |
| `tower11_step_lt` | every complete round strictly increases the tower |
| `defined_tree_eventually_lt11` | every W-definable tree stage is eventually below a full round |
| `fvalue_lt_round11` | every visible accepted kind-polymorphic program is below the round |

**Never evaluate any contender.**
