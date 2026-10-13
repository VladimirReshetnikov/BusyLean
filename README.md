# BusyLean: name the biggest number, in Lean

This is a Lean 4 edition of Cody Roux's
[name-the-biggest-number](https://github.com/codyroux/name-the-biggest-number)
contest; a snapshot of the original is in
[`docs/`](docs/name-the-biggest-number-master). The game is the same as in
[Scott Aaronson's essay](https://www.scottaaronson.com/writings/bignumbers.html):
name a bigger number than the previous contender. The number must be
**constructive**, and the claim must come with a **formal proof**. The only
change is that the proof assistant is Lean instead of Coq.

## Current contender: Contender 16

```lean
def family15 (n : Nat) : Nat := F15 (F15 n)                  -- Contender 15 = family15 42
def F16 (n : Nat) : Nat :=                                   -- BusyLean/Contender16.lean
  diagonalLift (schedule16 n) (family15 n + 1) tTransformer (fun _ => family15) n n
def contender_16 : Nat := F16 (F16 42)

theorem contender_15_lt_contender_16 : contender_15 < contender_16   -- BusyLean/Comparison16.lean
```

The ladder of universes becomes **transfinite**.

* [`SystemFL/Transfinite.lean`](BusyLean/SystemFL/Transfinite.lean):
  `FL.wfUniv` builds a universe for *every* well-founded atom order, by
  well-founded recursion: the domain of atom `a` is the sum of the semantics of
  all base kinds whose atoms lie below `a`. So the ladder language normalizes for
  ladders of any well-founded length.
* [`Ordinal/SortedLex.lean`](BusyLean/Ordinal/SortedLex.lean): the
  lexicographic order on non-increasing lists (Cantor normal forms) is
  well-founded whenever the exponents are accessible.
* [`Ordinal/OmegaPow.lean`](BusyLean/Ordinal/OmegaPow.lean): atoms are notations
  below `ω^ω`. At depth `n`, programs use levels up to `ω^(n-1)·n`; for example,
  the universe at `ω` holds operators from every finite level.
* The amplifier is Contender 15's rank hierarchy of lifts, seeded with
  Contender 15's family.

| Theorem | Statement |
|---|---|
| `FL.wfUniv` | a universe for every well-founded atom order |
| `Ordinal.wf_sorted` | sorted lists of accessible elements are well-founded lexicographically |
| `contender_15_lt_contender_16` | Contender 15 < Contender 16 |
| `family15_lt_F16` | Contender 15's family is beaten at every input |
| `tvalue_lt_F16` | every transfinite-ladder program of depth ≤ `n` is below `F16 n` |

## Contender 15

```lean
def family14 (n : Nat) : Nat := F14 (F14 n)                  -- Contender 14 = family14 42
def F15 (n : Nat) : Nat :=                                   -- BusyLean/Contender15.lean
  diagonalLift (schedule15 n) (family14 n + 1) flFamilyTransformer (fun _ => family14) n n
def contender_15 : Nat := F15 (F15 42)

theorem contender_14_lt_contender_15 : contender_14 < contender_15   -- BusyLean/Comparison15.lean
```

Contender 15 applies the strongest amplifier received so far to the strongest
language here.

* **Language:** the ladder of universes of Contender 14. `reflectFLFamily fs n`
  exceeds every visible coordinate of an oracle family and every level-`n`
  ladder program of depth `≤ n`; the programs see the whole family through a
  packed oracle.
* **Amplifier:** proposal P17's rank hierarchy of transformer lifts
  ([`HyperReflection.lean`](BusyLean/HyperReflection.lean), adopted
  unchanged; P20 found the same idea). Rank `k+1` traverses a schedule using
  rank `k` as the lift at every node. The schedule is
  `family14 n + 42` hyper-closures above `tree12`, and the rank is
  `family14 n + 1`.

| Theorem | Statement |
|---|---|
| `contender_14_lt_contender_15` | Contender 14 < Contender 15 |
| `family14_lt_F15` | Contender 14's family is beaten at every input |
| `fvalue_lt_F15` | every level-`n` ladder program of depth ≤ `n` is below `F15 n` |
| `diagonalLift_strictlyInflationary` | every rank strictly exceeds its base, with no monotonicity |

## Contender 14

```lean
def family13 (n : Nat) : Nat := F13 (F13 n)               -- Contender 13 = family13 42
def F14 (n : Nat) : Nat := FL.reflectFL family13 n        -- BusyLean/Contender14.lean
def contender_14 : Nat := F14 (F14 42)

theorem contender_13_lt_contender_14 : contender_13 < contender_14   -- BusyLean/Comparison14.lean
```

`reflectFL f n` exceeds `f n` and the value of every closed program of the
**level-`n` ladder language** of depth `≤ n` with the Church numeral type.
The level-`ℓ` language is Contender 13's dynamic-kind Fω plus atomic kinds
`dyn₀, …, dyn_{ℓ-1}`:

* atom `dyn_i` denotes the `dyn` of the level-`i` language;
* `apack a K A : a` and `aunpack a K X : K` move operators into and out of an
  atom from the kinds strictly below it, with `aunpack (apack A) ≡ A`. For
  example, an operator of kind `dyn₀ → ★` can be packed into `dyn₁`.

The syntax and the SN proof are parametric in a `Universe` of atoms (domains,
packing, reading, and the law `rd (pk v) = v`). So **one** theorem,
`FL.sn_of_typed`, normalizes every level. `FL.Univ f ℓ` builds level `ℓ` by
recursion ([`SystemFL/Ladder.lean`](BusyLean/SystemFL/Ladder.lean)). Input `n`
uses level `n`, so the reflection diagonalizes over the ladder itself.

| Theorem | Statement |
|---|---|
| `FL.sn_of_typed` | for every universe, every ladder term (with oracle) is strongly normalizing |
| `FL.infer_sound` | the checker is sound, for every atom type |
| `contender_13_lt_contender_14` | Contender 13 < Contender 14 |
| `family13_lt_F14` | Contender 13's family is beaten at every input |
| `fvalue_lt_contender_14` | every level-`F14 42` program of depth ≤ `F14 42` is exceeded |

## Contender 13

```lean
def family12 (n : Nat) : Nat := F12 (F12 n)               -- Contender 12 = family12 42
def F13 (n : Nat) : Nat := Fd.reflectFd family12 n        -- BusyLean/Contender13.lean
def contender_13 : Nat := F13 (F13 42)

theorem contender_12_lt_contender_13 : contender_12 < contender_13   -- BusyLean/Comparison13.lean
```

`reflectFd f n` exceeds `f n` and the value of every closed program of
**dynamic-kind System Fω** of depth `≤ n` with the Church numeral type. The
language adds a predicative universe of operators to kind-polymorphic Fω:

* a kind `dyn` whose elements are operators of *every* dyn-free kind
  (semantically `Σ k, Sem k`), with type-level `pack K A : dyn`,
  `unpack K X : K`, and `unpack K (pack K A) ≡ A`;
* kind variables at two levels. Level-1 variables range over kinds built from
  `dyn`, so programs can climb `dyn, dyn → ★, …` at run time (uniform orders
  ω + n).

Kinds still cannot quantify over kinds, so `dyn` never contains itself, and
the semantic SN proof (`Fd.sn_of_typed`) certifies consistency.

| Theorem | Statement |
|---|---|
| `Fd.sn_of_typed` | every dynamic-kind Fω term (with oracle) is strongly normalizing |
| `Fd.infer_sound` | the checker is sound |
| `contender_12_lt_contender_13` | Contender 12 < Contender 13 |
| `family12_lt_F13` | Contender 12's family is beaten at every input |
| `fvalue_lt_contender_13` | every program of depth ≤ `F13 42` is exceeded |

## Contender 12

```lean
def fkTransformer : Transformer := fun fs _ n => reflect11 fs n        -- BusyLean/Contender12.lean
def tree12 := Autonomous.realize (Autonomous.hyper 42 (Autonomous.encode index))
def F12 (n : Nat) : Nat := operatorStage fkTransformer tree12 (fun _ => family11) n n
def contender_12 : Nat := F12 (F12 42)                                  -- family11 n = F11 (F11 n)

theorem contender_11_lt_contender_12 : contender_11 < contender_12     -- BusyLean/Comparison12.lean
```

This contender reuses two ideas from the second batch of proposals (see
[the review](proposals/REVIEW.md)), with attribution, on top of this
repository's strongest language:

* **P6's operator stage**: reflection lifted to *transformers* of families,
  iterated along the index, with the lift itself iterated along a tree. It
  exponentiates where forest reflection multiplies.
* **P7's ordinal notations**: explicit Veblen-style closures stacked *above*
  Contender 6's language-defined index.
* The base transformer is Contender 11's reflection over **kind-polymorphic
  System Fω**.

| Theorem | Statement |
|---|---|
| `contender_11_lt_contender_12` | Contender 11 < Contender 12 |
| `family11_lt_F12` | Contender 11's family is beaten at every input |
| `fkTransformer_progressive` | kind-polymorphic Fω reflection is a progressive transformer |

## Contender 11

`F11 n = stage11 (fun _ => family10) index n`, `contender_11 = F11 (F11 42)`:
Contender 9's amplifier (forest reflection along the W-language's index)
applied to Contender 10's kind-polymorphic language. Theorems:
`contender_10_lt_contender_11`, `family10_lt_F11`, `defined_tree_eventually_lt11`.

## Contender 10

```lean
def family9 (n : Nat) : Nat := F9 (F9 n)                  -- Contender 9 = family9 42
def F10 (n : Nat) : Nat := Fk.reflectFk family9 n         -- BusyLean/Contender10.lean
def contender_10 : Nat := F10 (F10 42)

theorem contender_9_lt_contender_10 : contender_9 < contender_10   -- BusyLean/Comparison10.lean
```

`reflectFk f n` exceeds `f n` and the value of every closed program of
**kind-polymorphic System Fω** of depth `≤ n` with the Church numeral type.
Types may quantify over kinds (`∀κ. A`), so a single program can iterate
through kinds of unbounded order chosen at run time, via existential packages
`∃κ. B κ`. Proving such programs total needs candidates for all finite types
uniformly, beyond higher-order arithmetic (the limit of Fω).

* **Consistency and normalization** (`Fk.sn_of_typed`): kinds cannot quantify
  over kinds (no rule (△,□), so no Girard–Hurkens paradox). `∀κ. A` is modeled
  as a countable intersection over closed kinds.
* **Type checking** (`Fk.infer_sound`): Contender 8's sound checker plus kind
  abstraction and application.

| Theorem | Statement |
|---|---|
| `Fk.sn_of_typed` | every kind-polymorphic Fω term (with oracle) is strongly normalizing |
| `Fk.infer_sound` | the checker is sound |
| `contender_9_lt_contender_10` | Contender 9 < Contender 10 |
| `family9_lt_F10` | Contender 9's family is beaten at every input |
| `fvalue_lt_contender_10` | every program of depth ≤ `F10 42` is exceeded |

## Contender 9

```lean
def stage9 (seed : Family) : WTree ℕ → ℕ → ℕ               -- BusyLean/Contender9.lean
  | .leaf   => reflect9 seed
  | .node g => reflect9 (fun i => stage9 seed (g i))
def F9 (n : Nat) : Nat := stage9 (fun _ => family8) index n
def contender_9 : Nat := F9 (F9 42)                        -- family8 n = F8 (F8 n)

theorem contender_8_lt_contender_9 : contender_8 < contender_9   -- BusyLean/Comparison9.lean
```

Contender 6's forest reflection, with **System Fω** as the reflected language,
along Contender 6's index (every tree the W-language defines). A node's family
of child stages reaches Fω through the unary oracle as
`orc (2^i·(2m+1)) = fs i m` (`unpair2_code` proves the decoding). Informally
this is about f<sub>|Z_ω|·ψ(Ω_ω)²</sub>: a multiplicative step. The article
explains why the Calculus of Constructions would *not* be a growth-rate jump
over Fω, and why the next qualitative jump needs large elimination.

| Theorem | Statement |
|---|---|
| `contender_8_lt_contender_9` | Contender 8 < Contender 9 |
| `family8_lt_F9` | Contender 8's family is beaten at every input |
| `defined_tree_eventually_lt9` | every W-definable tree is eventually dominated |
| `unpair2_code` | the oracle-family code is decoded correctly |

## Contender 8

```lean
def family7 (n : Nat) : Nat := F7 (F7 n)                  -- Contender 7 = family7 42
def F8 (n : Nat) : Nat := Fw.reflectFw family7 n          -- BusyLean/Contender8.lean
def contender_8 : Nat := F8 (F8 42)

theorem contender_7_lt_contender_8 : contender_7 < contender_8   -- BusyLean/Comparison8.lean
```

`reflectFw f n` exceeds `f n` and the value of every closed **System Fω**
program of enumeration depth `≤ n` with the Church numeral type. Fω adds
*type operators* (kinds `★ | κ → κ`) to System F, reaching the strength of
higher-order arithmetic.

* **Normalization** (`Fw.sn_of_typed`): Girard's candidates lifted to kinds.
  The semantic domain of kind `κ₁ → κ₂` is the type of Lean functions between
  domains, so type-level β is literally function application.
* **Type checking** (`Fw.infer_sound`) decides type equality by comparing
  fuel-bounded type normal forms. It is sound (accepted programs are typable)
  and uses the syntax budget as fuel.
* The oracle is Contender 7's family, which Fω can amplify.

| Theorem | Statement |
|---|---|
| `Fw.sn_of_typed` | every System Fω term (with oracle) is strongly normalizing |
| `Fw.infer_sound` | the fuel-bounded type checker is sound |
| `contender_7_lt_contender_8` | Contender 7 < Contender 8 |
| `family7_lt_F8` | Contender 7's family is beaten at every input |
| `fvalue_lt_contender_8` | every Fω program of depth ≤ `F8 42` is exceeded |

## Contender 7

```lean
def F7 (n : Nat) : Nat := F.reflectF finalFamily n        -- BusyLean/Contender7.lean
def contender_7 : Nat := F7 (F7 42)

theorem contender_6_lt_contender_7 : contender_6 < contender_7   -- BusyLean/Comparison7.lean
```

`reflectF f n` exceeds `f n` and the value of every closed **System F**
program (Church-style, enumeration depth `≤ n`) of Church numeral type
`∀X. (X → X) → X → X`. Programs may call an oracle `orc : nat → nat`,
interpreted as `f`. A program's value is computed inside Lean: erase the
types, normalize, read off the numeral. Normalization is a total function
because of a formal **strong normalization theorem for System F**
(`F.sn_of_typed`), proved by Girard's reducibility candidates. The
impredicative quantification over candidates is legal because Lean's `Prop`
is impredicative.

* The oracle is Contender 6's family, so System F can amplify Contender 6
  with the strength of second-order arithmetic.
* The outer `F7` runs System F at a syntax budget larger than Contender 6.
* Informally, the numeric functions definable in System F are those provably
  total in second-order arithmetic Z₂, far beyond ψ(Ω_ω) (Contender 6's
  language).

| Theorem | Statement |
|---|---|
| `F.sn_of_typed` | every System F term (with oracle) is strongly normalizing |
| `F.infer_sound` | the type inferrer is sound for the erased term |
| `F.nstep_nf` | the normalizer's output is normal |
| `contender_6_lt_contender_7` | Contender 6 < Contender 7 |
| `finalFamily_lt_F7` | Contender 6's family is beaten at every input |
| `fvalue_lt_contender_7` | every System F program of depth ≤ `F7 42` is exceeded |

All of these use only `propext` and `Quot.sound`.

## Contender 6

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

| Theorem | Statement |
|---|---|
| `contender_5_lt_contender_6` | exact port of Contender 5 < Contender 6 |
| `p5_lt_contender_6` | proposal P5's number < Contender 6 |
| `p5Family_lt_finalFamily` | the same at every input `n` |
| `defined_tree_eventually_lt` | every tree the language defines is eventually dominated |
| `program_lt_finalFamily` | every program of depth ≤ n, run with the final oracles, is exceeded |
| `PortAgreement.largest_eq_oldMaximum` | P5's old-language port equals the exact port, at every depth |

These depend on `propext` only; the definition of `contender_5` uses no
axioms.

**Never evaluate any contender.** Checking the definitions and proofs does not
evaluate the numbers.

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
4. **Time budgets.** From a clean build directory, the new contender's
   definition must check in at most 15 s and its proof in at most 60 s, on a
   reasonable machine. The Lean core library may be precompiled, and so may
   the modules of earlier accepted contenders, which were checked under their
   own budgets. (Contenders build on their predecessors, so a fixed budget for
   the whole stack would eventually be exhausted by history alone.) The check
   script also reports the full clean-build time.
5. **No laziness.** Do not use the constant `contender_N` itself to define
   `contender_(N+1)`, and beat it by a large margin. The previous contender's
   *construction* (for example its family of functions) may appear as an
   oracle or seed of a qualitatively stronger construction, which makes the
   comparison formal. The audit checks that the constant itself is never
   mentioned.
6. **No shenanigans.** No exploits of the kernel, the elaborator or the
   toolchain.
7. **Toolchain.** Lean **4.34.0** (`lean-toolchain`). Libraries are allowed if
   widely used; this entry needs only Lean core.

## Checking

With [elan](https://github.com/leanprover/elan) installed:

```bash
python3 scripts/check.py
```

This deletes the build directories, builds the previous contender, times the
current contender's definition and proof phases against the budgets, reports
the total, and runs [`test/Audit.lean`](test/Audit.lean).
On an Intel i7-1355U (Windows 11), Contender 16's definition modules take
about 5 s and its proofs about 3 s; the full clean build of all contenders
takes about 49 s. Plain `lake build` also works, and
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
| [`BusyLean/SystemF/`](BusyLean/SystemF) | System F: syntax, reduction, types, candidates (SN), Church terms, normalizer |
| [`BusyLean/Contender7.lean`](BusyLean/Contender7.lean) | `fvalue`, `reflectF`, `contender_7` (definitions) |
| [`BusyLean/Comparison7.lean`](BusyLean/Comparison7.lean) | Contender 7 theorems |
| [`BusyLean/SystemFw/`](BusyLean/SystemFw) | System Fω: kinds and type β, typing, candidates over kinds (SN), sound checker |
| [`BusyLean/Contender8.lean`](BusyLean/Contender8.lean), [`Comparison8.lean`](BusyLean/Comparison8.lean) | Contender 8 definitions and theorems |
| [`BusyLean/Contender9.lean`](BusyLean/Contender9.lean), [`Comparison9.lean`](BusyLean/Comparison9.lean) | Contender 9 definitions and theorems |
| [`BusyLean/SystemFk/`](BusyLean/SystemFk) | kind-polymorphic Fω: syntax, typing, candidates with kind valuations (SN), sound checker |
| [`BusyLean/Contender10.lean`](BusyLean/Contender10.lean), [`Comparison10.lean`](BusyLean/Comparison10.lean) | Contender 10 definitions and theorems |
| [`BusyLean/Contender11.lean`](BusyLean/Contender11.lean), [`Comparison11.lean`](BusyLean/Comparison11.lean) | Contender 11 definitions and theorems |
| [`BusyLean/MetaReflection.lean`](BusyLean/MetaReflection.lean), [`MetaReflectionFacts.lean`](BusyLean/MetaReflectionFacts.lean) | operator-level reflection (adopted from P6) |
| [`BusyLean/Autonomous.lean`](BusyLean/Autonomous.lean) | ordinal notations above a tree (adopted from P7) |
| [`BusyLean/Contender12.lean`](BusyLean/Contender12.lean), [`Comparison12.lean`](BusyLean/Comparison12.lean) | Contender 12 definitions and theorems |
| [`BusyLean/SystemFd/`](BusyLean/SystemFd) | dynamic-kind Fω: syntax, typing, candidates with `dyn = Σ k, Sem k` (SN), sound checker |
| [`BusyLean/Contender13.lean`](BusyLean/Contender13.lean), [`Comparison13.lean`](BusyLean/Comparison13.lean) | Contender 13 definitions and theorems |
| [`BusyLean/SystemFL/`](BusyLean/SystemFL) | the ladder language, parametric in its atoms: syntax, typing, candidates over a `Universe` (SN), sound checker, the ladder of universes |
| [`BusyLean/Contender14.lean`](BusyLean/Contender14.lean), [`Comparison14.lean`](BusyLean/Comparison14.lean) | Contender 14 definitions and theorems |
| [`BusyLean/HyperReflection.lean`](BusyLean/HyperReflection.lean), [`HyperReflectionFacts.lean`](BusyLean/HyperReflectionFacts.lean) | rank hierarchy of transformer lifts (adopted from P17) |
| [`BusyLean/Contender15.lean`](BusyLean/Contender15.lean), [`Comparison15.lean`](BusyLean/Comparison15.lean) | Contender 15 definitions and theorems |
| [`BusyLean/Ordinal/`](BusyLean/Ordinal) | well-founded Cantor normal forms (sorted lists) and the atoms below `ω^ω` |
| [`BusyLean/Contender16.lean`](BusyLean/Contender16.lean), [`Comparison16.lean`](BusyLean/Comparison16.lean) | Contender 16 definitions and theorems |
| [`article/`](article) | research notes, LaTeX source and PDF |
| [`test/`](test) | axiom/dependency audit, smoke tests |
| [`proposals/`](proposals) | the twenty reviewed proposals and [the review](proposals/REVIEW.md) |
| [`incoming/`](incoming) | drop zone for new proposal archives ([how they are processed](incoming/README.md)) |
| [`docs/`](docs) | snapshot of the original Coq contest |

## History

| # | Proof assistant | Author | Idea |
|---|---|---|---|
| 4 | Coq | codyroux | `ack 5 42 10002`, Ackermann-style |
| 5 | Coq | samuelgruetter | largest STLC + natural recursion (System T) numeral of depth 42 |
| 6 | Lean | this repository | forest reflection over System T + finite-type W-types, along the language's own trees; it combines ideas from proposals P5, P2 and P4 |
| 7 | Lean | this repository | System F (impredicative polymorphism) with Contender 6 as oracle; strong normalization proved in Lean |
| 8 | Lean | this repository | System Fω (type operators) with Contender 7 as oracle; candidates over kinds |
| 9 | Lean | this repository | System Fω reflected along the W-language's own trees, seeded with Contender 8 |
| 10 | Lean | this repository | kind-polymorphic System Fω (unbounded orders at run time), seeded with Contender 9 |
| 11 | Lean | this repository | kind-polymorphic Fω reflected along the W-language's trees |
| 12 | Lean | this repository | operator-level reflection (from P6) along notations above the index (from P7), over kind-polymorphic Fω |
| 13 | Lean | this repository | dynamic-kind Fω: a predicative universe of operators, with two levels of kind variables |
| 14 | Lean | this repository | a ladder of such universes, one SN proof for all levels; input `n` uses level `n` |
| 15 | Lean | this repository | P17's rank hierarchy of transformer lifts over family-aware ladder reflection |
| 16 | Lean | this repository | a transfinite ladder (length `ω^ω`) via a universe for every well-founded atom order |

Proposals P1–P20 (four batches) were reviewed, rebuilt and ranked; see
[`proposals/REVIEW.md`](proposals/REVIEW.md). Upstream code is MIT-licensed
([`docs/.../LICENSE`](docs/name-the-biggest-number-master/LICENSE)); this
repository is MIT-0 ([`LICENSE`](LICENSE)).
