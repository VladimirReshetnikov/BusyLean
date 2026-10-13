## Current contender: Contender 11 (proposed)

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)
def F11 (n : Nat) : Nat :=
  stage11 (fun _ => family10) (crown11 (n + 1) index) n
def contender_11 : Nat := F11 (F11 42)

theorem contender_10_lt_contender_11 : contender_10 < contender_11
```

Contender 11 installs Contender 10's kind-polymorphic System Fω reflector at
every node of a well-founded forest.  It runs this forest reflection along the
self-generated W-tree index already used by Contenders 6 and 9, and puts an
input-diagonal crown of `n + 1` additional reflection nodes above the index.
The seed is Contender 10's *construction as a family*; the definition never
mentions the scalar `contender_10`.

The exact structural theorems include:

| Theorem | Statement |
|---|---|
| `family10_lt_F11` | Contender 10's family is beaten at every input |
| `stage11_crown_step_lt` | every consecutive crown level is strictly larger |
| `root_program_lt_F11` | every accepted depth-bounded Fk program relative to the preceding crown is exceeded |
| `defined_tree_eventually_lt11` | every W-language-defined tree is eventually dominated |
| `contender_10_lt_contender_11` | the required scalar comparison |

Do not evaluate any contender.
