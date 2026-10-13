# BusyLean: name the biggest number, in Lean

This is a Lean 4 edition of Cody Roux's
[name-the-biggest-number](https://github.com/codyroux/name-the-biggest-number)
contest; a snapshot of the original is in
[`docs/`](docs/name-the-biggest-number-master). The game is the same as in
[Scott Aaronson's essay](https://www.scottaaronson.com/writings/bignumbers.html):
name a bigger number than the previous contender. The number must be
**constructive**, and the claim must come with a **formal proof**. The only
change is that the proof assistant is Lean instead of Coq.

## Current contender: Contender 6

```lean
def contender_6 : Nat := stage p5Family index 42        -- BusyLean/Contender6.lean

theorem contender_5_lt_contender_6 : contender_5 < contender_6   -- BusyLean/Comparison.lean
```

It is built in three layers:

1. **Object language.** System T extended with W-types `W A` over every
   finite type `A` (`W ℕ`, `W (W ℕ)`, `W (ℕ → W ℕ)`, …), each with a recursor
   into every type. It is evaluated by a total interpreter on raw terms. This
   language is taken from proposal P5. Its strength is roughly ψ(Ω_ω), the
   ordinal of ID<sub>&lt;ω</sub>, far beyond System T's ε₀.
2. **Forest reflection.** `reflect fs n` exceeds every oracle value `fs i n`
   (`i ≤ n`) and every program of depth `≤ n`, run *relative to the oracle
   family `fs`*. The oracle is simply the outermost variable `var 0`.
   `stage seed a` iterates this along a tree `a : W ℕ`: a node reflects over
   the family of its children's stages, so any child can be called at a
   dynamically computed index.
3. **A self-referential index.** `index` joins *every* `W ℕ` tree that a
   closed program of the language defines. The hierarchy therefore climbs
   through the language's own ordinals, not through a hand-written notation
   system.

The seed `p5Family` is P5's number as a function of its input, so beating
P5 is a theorem (`p5_lt_contender_6`). An informal fast-growing-hierarchy
estimate is f<sub>|L|·|L|</sub>(42) with |L| ≈ ψ(Ω_ω); for comparison, P5 is
about f<sub>|L|+ω²</sub>(42) and Contender 5 about f<sub>&lt;ε₀</sub>(42).

**Never evaluate `contender_6` (or `contender_5`).** Checking the definitions
and proofs does not evaluate either number.

### Verified results

| Theorem | Statement |
|---|---|
| `contender_5_lt_contender_6` | exact port of Contender 5 < Contender 6 |
| `p5_lt_contender_6` | proposal P5's number < Contender 6 |
| `p5Family_lt_finalFamily` | the same at every input `n` |
| `defined_tree_eventually_lt` | every tree the language defines is eventually dominated |
| `program_lt_finalFamily` | every program of depth ≤ n, run with the final oracles, is exceeded |
| `PortAgreement.largest_eq_oldMaximum` | P5's old-language port equals the exact port, at every depth |

All of these depend on `propext` only; the definition of `contender_5` uses no
axioms. The audit also checks that the definition of `contender_6` never
mentions `contender_5` or its winner-selection functions.

## Rules (Lean edition)

These are adapted from the [original rules](docs/name-the-biggest-number-master/README.md):

1. **Constructive numbers only.** The number must be a closed, computable
   `Nat` definition. No Busy Beavers or other oracles, and no `noncomputable`,
   `partial`, `unsafe`, `opaque` stand-ins, `implemented_by` or `extern`.
2. **Formal proof.** Submit a definition `contender_N : Nat` and a theorem
   `contender_(N-1)_lt_contender_N`. When the previous contender was written
   in another proof assistant, compare against a faithful port and document
   the port.
3. **Axioms.** Only `propext` and `Quot.sound` (hence `funext`) are allowed.
   `Classical.choice`, `sorryAx` and custom axioms are not. Check with
   `#print axioms`. `native_decide` is not allowed either.
4. **Time budgets.** From a clean build directory (the Lean core library
   may be precompiled), the definition and everything it imports must check
   in at most 15 s, and the proof in at most 60 s, on a reasonable machine.
5. **No laziness.** Do not use `contender_N` itself to define
   `contender_(N+1)`; beat it by a large margin.
6. **No shenanigans.** No exploits of the kernel, the elaborator or the
   toolchain.
7. **Toolchain.** Lean **4.34.0** (`lean-toolchain`). Libraries are allowed if
   widely used; this entry needs only Lean core.

## Checking

With [elan](https://github.com/leanprover/elan) installed:

```bash
python3 scripts/check.py
```

This deletes the build directories, times the definition and proof phases
against the budgets, and runs [`test/Audit.lean`](test/Audit.lean).
On an Intel i7-1355U (Windows 11) the definitions take about 5 s and the
proofs about 5–6 s. Plain `lake build` also works, and
`lake env lean test/Contender5Smoke.lean` checks the port against the
reference small-depth table (maxima 0, 0, 1, 2, 3 at depths 0–4).

## Repository layout

| Path | Contents |
|---|---|
| [`BusyLean/Contender5.lean`](BusyLean/Contender5.lean) | definition-by-definition port of `Contender.v` and `contender_5` |
| [`BusyLean/PortAgreement.lean`](BusyLean/PortAgreement.lean) | logical-relation proof that P5's port agrees with it |
| [`BusyLean/Reflection.lean`](BusyLean/Reflection.lean) | oracle relativization, `reflect`, `stage` (definitions) |
| [`BusyLean/ReflectionFacts.lean`](BusyLean/ReflectionFacts.lean) | their inequalities |
| [`BusyLean/Contender6.lean`](BusyLean/Contender6.lean) | `index`, `p5Family`, `contender_6` (definitions) |
| [`BusyLean/Comparison.lean`](BusyLean/Comparison.lean) | all Contender 6 theorems |
| [`test/`](test) | axiom/dependency audit, smoke tests |
| [`proposals/`](proposals) | the five reviewed proposals and [the review](proposals/REVIEW.md) |
| [`docs/`](docs) | snapshot of the original Coq contest |

## History

| # | Proof assistant | Author | Idea |
|---|---|---|---|
| 4 | Coq | codyroux | `ack 5 42 10002`, Ackermann-style |
| 5 | Coq | samuelgruetter | largest STLC + natural recursion (System T) numeral of depth 42 |
| 6 | Lean | this repository | forest reflection over System T + finite-type W-types, along the language's own trees; it combines ideas from proposals P5, P2 and P4 |

Proposals P1–P5 were reviewed, rebuilt and ranked; see
[`proposals/REVIEW.md`](proposals/REVIEW.md). Upstream code is MIT-licensed
([`docs/.../LICENSE`](docs/name-the-biggest-number-master/LICENSE)); this
repository is MIT-0 ([`LICENSE`](LICENSE)).
