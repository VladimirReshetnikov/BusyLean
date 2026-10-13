# Formal claims and status map

## Construction

Let `fs : W.Family`.

```lean
def reflect11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))

def towerFk : Nat -> (Nat -> Nat) -> Nat -> Nat
  | 0, f => f
  | k + 1, f => Fk.reflectFk (towerFk k f)

def diagonal11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (reflect11 fs n)
    (towerFk (reflect11 fs n + 1) (reflect11 fs) n)
```

`stage11` places `diagonal11` at every node of a W-tree. The final seed and number are:

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)
def F11 (n : Nat) : Nat := stage11 (fun _ => family10) index n
def contender_11 : Nat := F11 (F11 42)
```

## Exact theorem targets encoded in Lean

| Declaration | Claim |
|---|---|
| `oracle_lt_reflect11` | `fs i n < reflect11 fs n` for `i <= n`. |
| `fvalue_lt_reflect11` | Every term in `Fk.ctmsUpTo n` evaluates below `reflect11 fs n` relative to `packFamily fs`. |
| `input_lt_reflect11` | `n < reflect11 fs n`. |
| `towerFk_step_lt` | Every added `Fk.reflectFk` layer strictly increases the value at every input. |
| `towerFk_strictMono` | Tower value is strictly monotone in the height. |
| `fixedTower_lt_diagonal11` | Every height `k <= reflect11 fs n` is dominated by `diagonal11 fs n`. |
| `oracle_lt_diagonal11` | Every visible child is dominated by the node diagonal. |
| `stage11_child_lt` | Every visible child stage is strictly below its parent stage. |
| `family10_lt_F11` | `family10 n < F11 n` at every input. |
| `contender_10_lt_contender_11` | The incumbent closed number is strictly smaller than the proposal. |
| `defined_tree_eventually_lt11` | Every W-language-denoted tree is eventually dominated inside the final forest family. |

## Mathematical proof of the central comparison

1. `family10 42` is definitionally `contender_10`.
2. A fixed path inside `index` reaches `leaf`: outer child 0, then depth-0 child 0.
3. The seed value is below the leaf stage by node oracle domination.
4. Each of the two tree edges is strict by `stage11_child_lt`.
5. Hence `contender_10 < F11 42`.
6. Every stage strictly exceeds its input, so `F11 42 < F11 (F11 42)`.
7. The latter is definitionally `contender_11`.

No informal ordinal estimate is used in this proof.

## Computability claim

The proposed value is computable in principle because it is built from:

- finite syntax enumerations;
- a decidable bounded type checker;
- the previously formalized total normalizer;
- finite maxima and finite prefixes;
- primitive recursion on a natural tower height; and
- structural recursion on the existing W-tree type.

No halting oracle, unbounded program maximum, `noncomputable` definition, unsafe primitive, custom axiom, or external implementation is introduced.

## Claims deliberately not made

This archive does not claim:

- an exact proof-theoretic ordinal for Contender 11;
- a formal separation from every function definable in an external theory;
- practical evaluability;
- or successful Lean 4.34.0 kernel replay in the artifact-building container.

The first two are open metamathematical directions. The last item must be resolved by running the included checker in the pinned repository.
