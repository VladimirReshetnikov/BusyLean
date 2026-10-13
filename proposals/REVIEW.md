# Review of the five incoming proposals

All five proposals target the same goal: a closed Lean term `contender_6 : Nat`
with a kernel-checked proof that it exceeds a Lean port of Contender 5. That is
the largest numeral produced by a raw Gödel System T term of syntax depth ≤ 42,
from [`Contender.v`](../docs/name-the-biggest-number-master/Contender.v).

Every proposal was rebuilt from source here, on **Lean 4.34.0** (the locally
installed toolchain; Lean 4.19.0, which most proposals pinned, is not
installed). Rules applied: those of the [Lean edition](../README.md#rules-lean-edition),
where the permitted axioms are `propext` and `Quot.sound`.

## Build and audit results

Machine: Intel i7-1355U, Windows 11. Times are clean `lake build`s of *all*
modules of the proposal (definitions, proofs, smoke tests), so each one bounds
both the definition and the proof budget from above.

| | Archive | As delivered | Repairs needed | Clean build | Axioms of `contender_6` and the comparison |
|---|---|---|---|---:|---|
| P1 | `Lean_Big_Number.zip` | compiles | none (toolchain pin only) | 11.9 s | `propext` |
| P2 | `Lean_Contender_6.zip` | compiles | none (pin + lakefile) | 10.2 s | `propext` |
| P3 | `lean_big_number (2).zip` | compiles | none (pin + lakefile) | 13.9 s | `propext` |
| P4 | `lean_big_number_research.zip` | **does not compile** (author-declared) | 4 local fixes | 15.4 s | `propext` |
| P5 | `lean_w_reflection_research.zip` | **does not compile** (author-declared) | 3 local fixes | 4.2 s | `propext` |

The repairs are in their own commits and change no definition's meaning. They
are the same three kinds in P4 and P5:

1. numerals at `den .nat` need a `(0 : Nat)` ascription (`den` is not reducible
   during elaboration);
2. direct uses of `Tree.rec` / `WTree.rec` must become structural pattern
   matches, because the code generator rejects raw recursors;
3. the strict-comparison proofs made the unifier try to *normalize* Contender 5
   or the new number. They were restated so that only δ-unfolding is needed.

**Note on axioms.** P1–P3 report empty axiom lists on 4.19.0. On 4.34.0,
`propext` appears in all five, for toolchain reasons:

* wildcard match arms now compile to `_sparseCasesOn` helpers that use
  `Nat.land`, and the termination proof of `Nat.bitwise` uses `propext`;
* the core accessor `xs[i]?` (`List.get?Internal`) is compiled the same way;
* several core lemmas (`Nat.le_max_left`, `List.mem_append`, …) now depend
  on `propext`.

Setting `backward.match.sparseCases false` removes the first source only. No
proposal depends on `Quot.sound` or `Classical.choice`. All five therefore
pass the axiom rule.

## What each proposal actually builds

The size of the final number is decided by two things. The first is the
**object language** whose bounded-depth maximum is taken; its strength is
measured by a proof-theoretic ordinal |L|. The second is the **amplifier**
stacked on top. A reflection step (relativizing L to an oracle f_β) adds
about |L| to the ordinal (β ↦ β + |L|). Iterating it along an index tree of
height α therefore only *multiplies*: β + |L|·α. Explicit ordinal notations
without collapsing functions stay below the Bachmann–Howard ordinal BH. All
estimates below are informal fast-growing-hierarchy calibrations, not
theorems.

### P1 — amplifier over explicit tree notations
`fast b a n` is a fast-growing hierarchy over Brouwer trees built from
hand-written Veblen-style operators (`veblenTree`, `gammaSeed`, higher-type
`omegaIteration`), with base `b` = the System T maximum (≈ f_{ε₀}). Numerical
"tower feedback" chooses iteration counts. Growth ≈ f_{ε₀+α}, where α is the
index notation's ordinal (around Γ₀ and beyond, but below BH). Proved bonus:
`towerFeedback (C5+1) (C5+1) ≤ contender_6`.

### P2 — forest reflection
The object language is System T + Brouwer trees (with recursion into all finite
types) + an oracle family, so |L| ≈ BH. Reflection is iterated along a tree
schedule built from higher-type Veblen-style functionals, keeping each child's
function separately accessible at limits. Growth ≈ f_{BH·α}, α < BH. This is
the most carefully engineered of the compiled entries (288 audited
declarations, non-representability theorem).

### P3 — reflection tree
The language is System T + a unary oracle + quoted old terms (|L| ≈ ε₀).
Reflection runs along Veblen-style trees. Growth ≈ f_{ε₀·α}, α < BH. Proved
bonus: a five-fold exponential lower bound over C5.

### P4 — ramified reflection
The language matches P2's in strength (T + Brouwer trees + binary oracle +
quoted old terms, |L| ≈ BH). Reflection runs along `grandIndex`, a tree built
from finite-type iteration functionals with numerical feedback.
Growth ≈ f_{BH·α}, α < BH.

### P5 — W-reflection
The language is System T + **W-types `W A` over every finite type `A`**,
including `W (W ℕ)`, `W (ℕ → W ℕ)`, …, with recursion into every type. That
gives a hierarchy of tree classes at all finite levels, so |L| ≈ ψ(Ω_ω)
(the strength of ID_{<ω}), far above BH·BH. The amplifier on top is weak (two
diagonalizations and a 42-fold iteration, about +ω² in ordinal terms).

## Ranking

1. **P5**: ≈ f_{ψ(Ω_ω)+ω²}. Its base language alone dominates everything else:
   ψ(Ω_ω) > ψ(Ω₂) ≫ BH·BH.
2. **P2 ≈ P4**: ≈ f_{BH·α} for explicit-notation α < BH. I did not determine
   their relative order; both are far below P5.
3. **P3 ≳ P1**: reflection over T multiplies (ε₀·α), while P1's hierarchy over
   a T base mostly adds (ε₀+α). Both are below BH.

Step 1 is robust: it compares object-language ordinals that differ by
collapsing levels. Steps 2 and 3 compare amplifiers of similar shape and are
less certain.

## Outcome

None of the five is adopted unchanged. P5 has the strongest idea, but it was
uncompiled and barely amplified. The adopted Contender 6
([`BusyLean/Contender6.lean`](../BusyLean/Contender6.lean)) **combines** their
ideas:

* P5's W-language (the strongest base) as the object language,
* relativized to an oracle *family* with dynamic index access (P2's forest
  reflection) and iterated along a tree index (P2, P4),
* where the index ranges over **every tree the W-language itself defines**,
  which is new. This raises the index from an explicit notation (< BH) to the
  language's own ordinal, for growth ≈ f_{ψ(Ω_ω)·ψ(Ω_ω)},
* seeded with P5's own family, so `P5 < Contender 6` is a *formal* theorem,
  not just an ordinal estimate.

The comparison with Contender 5 uses an exact, independent Lean port of
`Contender.v` ([`BusyLean/Contender5.lean`](../BusyLean/Contender5.lean)).
[`BusyLean/PortAgreement.lean`](../BusyLean/PortAgreement.lean) proves that P5's
numerical port of the old language agrees with it at every depth. That settles
the one fidelity question P5 had left open.

Candidly, the price of the formal margin over P5 is that Contender 6's
definition contains P5's family, and with it P5's seed guard
`max (oldMaximum n) (wMaximum n)`. That guard is the old language's maximum as
a function of depth, not the constant `contender_5`. `test/Audit.lean`
machine-checks that the definition never mentions `contender_5`, the `maxBy`
winner, or either proposal-level contender constant.

---

# Second batch: P6–P10

Five more archives arrived, all proposing a "Contender 7" on top of this
repository's **Contender 6**, at base commit `86b3606`. That predates
Contenders 7–11, so none of them knows about the System F, Fω or
kind-polymorphic contenders.

## Build and audit results

Each proposal was built with Lean 4.34.0. P6 and P7 are overlays on a scratch
git worktree at their base commit. P8 requires that commit through a GitHub
`require`; its lakefile was pointed at the same local worktree, so nothing was
fetched. P9 and P10 are standalone. P9 needed a one-line harness fix: its
lakefile listed only `BusyLean.Contender6` as a root, so `BusyLean.Reflection`
was never built. My own axiom checks were run; the proposals' scripts were not.

| | Archive | Author's status | Definitions | Proofs | Axioms of `contender_7` / comparison | Clean build |
|---|---|---|---|---|---|---:|
| P6 | `BusyLean_Contender7.zip` | uncompiled | compile | **compile** | `propext` / `propext, Quot.sound` | 12.9 s |
| P7 | `…_AutonomousReflection.zip` | CI-verified | compile | **compile** | `propext` / `propext` | 8.7 s |
| P8 | `…_Ramified_Worlds.zip` | uncompiled | compile | fail (`Proofs.lean:174`, type mismatch) | n/a | n/a |
| P9 | `…_Research.zip` | uncompiled | compile | fail (`Enumeration.lean`, 9 `omega` failures) | n/a | n/a |
| P10 | `BusyLean_Semantic_Mirror.zip` | uncompiled | compile (`Mirror.Model`) | fail (`Growth.lean`, `Semantics.lean`) | n/a | n/a |

P6 is correct as delivered, even though its author could not compile it. For
P8–P10, the comparison theorems with Contender 6 are therefore unverified. I
did not repair them, because the size comparison below does not depend on
them.

## What they build

All five keep Contender 6's object language, P5's W-language with
|L| ≈ ψ(Ω_ω), and add an amplifier.

* **P6, operator reflection.** It lifts reflection from families to
  *transformers* of families. `runTransformer op seed a` iterates a transformer
  along a tree; `liftTransformer` runs it along Contender 6's index; and
  `operatorStage` iterates the lift itself along another tree. Each lift
  multiplies the number of reflection steps by the index height, so the
  operator stage *exponentiates*: about |L|^|L|, against |L|·|L| for
  Contender 6. All comparisons follow from one property, `Progressive op`
  (every visible seed value lies below every output), so the machinery is
  generic in the base reflection.
* **P7, critical-point reflection.** Contender 6's index is a real Lean tree,
  so explicit ordinal functions can be applied *on top of the language's own
  ordinal*. It defines ω-powers, derivatives, a finite critical hierarchy, a
  Γ-like common critical closure, and 42 higher derivatives above the encoded
  index. The index height thus grows from |L| to a Γ-like closure above |L|.
* **P8, P9, P10, worlds and models.** They expose a lower world's whole
  hierarchy operator, or a model with its own tree generator, to the next
  world's programs, then iterate or bootstrap along self-generated trees.
  Each world can run the previous hierarchy along any tree it builds. The
  trees themselves stay below |L|·ω, so each round multiplies by about |L|.
  The bootstraps reach roughly |L|^ω, or an ε-type closure above |L|.

## Comparison with the current contenders

Every construction in this batch is an amplifier over a ψ(Ω_ω)-strength
language. Their ordinals, from |L|^|L| up to Γ-type closures above |L|, lie far
below the proof-theoretic ordinal of second-order arithmetic. By the "base
language dominates" heuristic, all five are therefore **vastly smaller than
Contender 7** (System F, ≈ f_{|Z₂|} at an input beyond Contender 6). They are
smaller still than Contenders 8–11 (Fω, Fω reflected along trees,
kind-polymorphic Fω, and its reflection). This comparison is informal: no
theorem relates their constants to mine.

## Ideas reused

Two ideas are generic and compose with the stronger languages:

1. **P6's operator-level reflection.** Instantiated with the kind-polymorphic
   Fω reflection of Contender 11 as its base transformer, it is progressive by
   the same one-line argument.
2. **P7's explicit ordinal notations above the language-defined index.** They
   serve as the tree along which the operator stage runs.

Contender 12 combines both, with attribution in the source. The world/model
constructions of P8–P10 require an object language that manipulates trees as
data. The W-language qualifies, but System F, Fω and Fk do not, since they
have no set-theoretic model. These ideas are recorded for a future
tree-capable language.

---

# Third batch: P11–P16

Six more archives arrived. P11–P15 propose a "Contender 11" over this
repository's Contender 10 (kind-polymorphic Fω, commit `4c4b03d`). P16 is a late
"Contender 7" over Contender 6 (commit `86b3606`). None of them knows about
Contenders 11–13 as they now exist here.

## Build and audit results

Each proposal was overlaid on a scratch git worktree at its base commit and
built with Lean 4.34.0 (`lake build BusyLean.Comparison11`, or `Comparison7`
for P16). The axiom checks are my own; the proposals' scripts were not run.

| | Archive | Author's status | Definitions | Proofs | Axioms of `contender_N` / comparison |
|---|---|---|---|---|---|
| P11 | `BusyLean_Contender11.zip` | uncompiled | compile | **compile** | `propext, Quot.sound` / same |
| P12 | `…_Crowned_Forest.zip` | uncompiled | compile | fail: type mismatch at `Comparison11.lean:77`, max recursion depth at `:149` | n/a |
| P13 | `…_DRKR_Research_Package.zip` | uncompiled | compile | **did not terminate**: stopped after more than 5 CPU-minutes, far beyond the 60 s proof budget | n/a |
| P14 | `…_DiagonalForest.zip` | uncompiled | compile | **compile** | `propext, Quot.sound` / same |
| P15 | `…_ForestFk.zip` | merged-source check claimed | compile | **compile** | `propext, Quot.sound` / same |
| P16 | `busylean_reflection_power_research.zip` | uncompiled | compile | fail: max recursion depth at `Comparison7.lean:99` | n/a |

The failures share one cause, the trap described in the article's
engineering lessons. A proof step makes the elaborator compare or unfold a
term containing a contender-sized number. P16's `change` relates
`metaHeight` to `Nat.succ (42 + p5Family 0 42)`, and its comment says it
"unfolds only the successor guard", but the definitional check evaluates
`p5Family 0 42`. P13's `simpa [RK.ramified]` and its `rfl` relating
`contender_10 + 1` to `family10 42 + 1` invite the same normalization at a
giant rank.

## What they build

All six keep an earlier language: Fk (|Fk|) for P11–P15, and the W-language
(|L| ≈ ψ(Ω_ω)) for P16. The amplifiers on top are:

* **P11, self-accelerated tower.** Complete forest-reflection rounds along
  the index, iterated a self-fed finite number of times: ≈ |Fk|·|L|·ω.
* **P12, crowned forest.** The index plus an input-diagonal chain above it:
  ≈ |Fk|·(|L|+ω).
* **P13, ramified kind reflection.** The autonomous lift along the index,
  iterated up to rank `family10 n + 1`: ≈ |Fk|·|L|^ω.
* **P14, self-height diagonal forest.** Reflection towers whose height is a
  previous reflection value, placed along the index: ≈ |Fk|·|L|·ω.
* **P15, forest reflection of Fk.** Its construction is identical to this
  repository's Contender 11: ≈ |Fk|·|L|².
* **P16, reflection power.** Whole schedulers reflected repeatedly along the
  index over the W-language: an amplifier of Contender 6, ≈ |L|^ω.

## Comparison with the current contenders

Every amplifier in this batch is at most Contender 12's: Contender 12 iterates
the same autonomous lift along a Γ-like *tree*, not a finite rank, which
gives about |Fk|·|L|^(Γ-closure). Contender 13 changes the language itself, to
dynamic-kind Fω with uniform orders ω+n, which by the "base language
dominates" heuristic exceeds every |Fk|-based amplification. Informally, the
whole batch is therefore below Contender 12, and well below Contender 13. P16
is a W-language construction, far below Contender 7. No theorem relates
their constants to mine.

## Ideas

Self-fed iteration counts (P11, P14), crowns (P12) and finite diagonal ranks
(P13) each add about a factor of ω to the index ordinal. They are subsumed
by the tree-indexed operator stage of Contender 12, so nothing in this batch
is adopted. P15 independently arrived at Contender 11's exact construction,
which corroborates it.

# Fourth batch: P17–P20

Four archives arrived, all proposing a "Contender 14" over Contender 13
(dynamic-kind Fω, Fd), written against commit `1ee50c7`. They predate this
repository's Contender 14, the ladder of universes. Each defines `family13 n =
F13 (F13 n)` and a *family-aware* Fd reflection: Fd programs receive a packed
oracle family, and a prefix maximum makes the transformer progressive without
monotonicity.

## Build and audit results

Each proposal was overlaid on a scratch worktree at `1ee50c7` and built with
Lean 4.34.0 (`lake build BusyLean.Contender14`, then `BusyLean.Comparison14`).
The axiom, closure and per-module checks are my own; the proposals' audit
files and scripts were not run. Timings are for the new modules only, with
the base precompiled.

| | Archive | Author's status | Definitions | Proofs | Axioms (`contender_14`, comparison, every new constant) |
|---|---|---|---|---|---|
| P17 | `…_DiagonalHyperreflection.zip` | CI-validated | compile, 0.5 s | **compile**, 0.5 s | `propext, Quot.sound` |
| P18 | `…_DiagonalOperatorTower.zip` | static validation only | compile, 1.6 s | fail: type mismatch at `Comparison14.lean:81` | n/a as submitted |
| P19 | `…_RDOR.zip` | build receipt template | compile, 1.3 s | **compile**, 2.2 s | `propext, Quot.sound` |
| P20 | `…_RankDiagonal.zip` | "Lean not run" | compile, 4.2 s | **compile**, 1.7 s | `propext, Quot.sound` |

The closure of each `contender_14` (about 1,920 constants) avoids
`contender_5` … `contender_13`. P18's failure is cosmetic. `simpa [f,
schedule14] using h2` normalizes `operatorStage base .leaf` differently from
the goal's `liftTransformer base`, although the two are definitionally equal.
Replacing it with `exact h2` makes the proof module compile, and the audit
then passes with the same axioms. That repair was only tested on the scratch
worktree; the imported sources are unmodified.

## What they build

Write τ for the autonomous schedule above `tree12` (a Γ-like closure over the
W-language's index) and |Fd| for the dynamic-kind language's ordinal. Every
proposal keeps Fd as its language and amplifies the index ordinal:

* **P17, diagonal hyperreflection.** A hierarchy of *transformer lifts*. Rank 0
  is the autonomous lift. Rank k+1 traverses the schedule using rank k as the
  lift at every node, and also pre-amplifies the base with rank k. Each rank
  roughly exponentiates the previous one, and the rank is diagonalized at
  `family13 n + 1`: about |Fd|·ε(τ).
* **P18, diagonal operator tower.** Operator stages stacked to height
  `family13 n`. Each level wraps the previous transformer in a stage along a
  schedule with a leaf at branch 0: about |Fd|·τ^ω.
* **P19, ramified dynamic operator reflection.** Feedback steps
  `towerStep base = operatorStage base tree14 ∘ base`, stacked to height n+1,
  with `tree14` one more hyper-closure above `tree12`. The seed includes all
  finite iterations of F13: about |Fd|·τ^ω.
* **P20, bi-diagonal rank reflection.** The same idea as P17, found
  independently: `rankLift (r+1)` lifts a splice whose branches are
  `metaStage (rankLift r)` along the schedule, diagonalized at
  `family13 n + 1`. About |Fd|·ε(τ).

## Comparison with the current contenders

Each proposal proves `contender_13 < contender_14` for its own number. So
informally all four exceed Contender 13, with P17 ≈ P20 > P18 ≈ P19.

The repository's Contender 14 changes the language instead: the ladder of
universes, with level n at input n. By the "base language dominates"
heuristic, the ladder exceeds every |Fd|-based amplification. A stronger
language proves that recursive amplifications over the weaker language
terminate. The whole batch is therefore informally below this repository's
Contender 14. No theorem relates their constants to mine (they are all named
`contender_14`).

## Ideas adopted

The rank hierarchy of lifts (P17, independently P20) is the strongest generic
amplifier received so far. It strictly generalizes the single operator stage
of Contender 12, and its proofs are short and generic over `Transformer`.
Contender 15 adopts P17's `HyperReflection` and `HyperReflectionFacts`
modules, with attribution, and applies them to a family-aware **ladder**
reflection seeded with Contender 14's family. That combines both routes: the
strongest language here and the strongest amplifier received.

# Late arrival: P21

One more archive, `BusyLean_Contender14_SelfHeight_Fd_Operator_Power.zip`,
proposes a "Contender 14" over Contender 13 (commit `0cd13c0`). It arrived
after this repository's Contenders 14–20.

## Build and audit

Overlaid on a scratch worktree at `0cd13c0` and built with Lean 4.34.0, with
the reviewer's own audit:

| | Author's status | Definitions | Proofs | Axioms (`contender_14`, comparison, every new constant) |
|---|---|---|---|---|
| P21 | "not kernel-compiled" | compile, 2.3 s | **compile**, 1.7 s | `propext, Quot.sound` |

The closure of its `contender_14` (1,913 constants) avoids `contender_5` …
`contender_13`.

## What it builds

`F14 n = operatorPower tree14 fdTransformer (family13 n + 1) (fun _ => family13)
(family13 n) (family13 n)`. This is a tower of operator stages along
`tree14 = realize (hyper 42 (encode tree12))`, whose height is the
self-referential value `family13 n + 1`, over family-aware Fd reflection. It
belongs to the same class as P18 and P19: about |Fd|·τ^ω.

## Comparison

It proves `contender_13 < contender_14` for its own number. Informally it is
below P17/P20, whose rank hierarchy of lifts already subsumes towers of stages,
and therefore below this repository's Contender 14 (the ladder language). It
is far below the current Contender 20. Nothing new is adopted: the
self-height parameter is the same diagonal device Contender 15 uses for its
rank.

# Late arrival: P22

`BusyLean_Contender20_WRanked_Hyperreflection.zip` proposes a "Contender 20"
over Contender 19 (base commit `64d31a0`). It arrived after this repository's
Contenders 20–22.

## Build and audit

Overlaid on a scratch worktree at `64d31a0` and built with Lean 4.34.0, with
the reviewer's own audit:

| | Author's status | Definitions | Proofs | Axioms (`contender_20`, comparison, every new constant) |
|---|---|---|---|---|
| P22 | CI-validated | compile, 2.9 s | **compile**, 1.2 s | `propext, Quot.sound` |

The closure of its `contender_20` (4,186 constants) avoids `contender_5` …
`contender_19`.

## What it builds

It generalizes P17's rank hierarchy of lifts from natural-number ranks to
**well-founded W-tree ranks**:

```lean
def wDiagonalLift (schedule : WTree Nat) : WTree Nat → TransformerLift
  | .leaf => liftTransformer
  | .node f =>
      let lower := spliceLifts (fun i => wDiagonalLift schedule (f i))
      fun base => stageLift lower (lower base) schedule
```

At a node, the lifts of all children are spliced into one lift. That lift both
pre-amplifies the base and serves as the local lift along the schedule. The
rank tree is an autonomous notation above the schedule
(`realize (hyper (family19 n + 42) (encode (schedule20 n)))`), so the rank is a
large countable ordinal rather than `ω`. Over Contender 19's large-Veblen
ladder this gives about |FL_LVO|·(lift hierarchy of transfinite rank).

## Comparison and adoption

It proves `contender_19 < contender_20` for its own number. It keeps
Contender 19's language, so by the base-language heuristic it is below this
repository's Contender 20 (the Bachmann–Howard ladder) and its successors.

The transfinite rank is a genuine improvement of the amplifier, and it composes
with any ladder. **Adopted** in Contender 23: `TreeHyperReflection` and its
facts are taken unchanged, with attribution, and applied to Contender 22's
tower ladders.

# Late arrival: P23

`BusyLean_Contender20_ThirdOrder_Hyperreflection.zip` proposes a "Contender
20" over Contender 19 (base commit `64d31a0`). It arrived after this
repository's Contenders 20–24.

## Build and audit

| | Author's status | Definitions | Proofs | Axioms (`contender_20`, comparison, every new constant) |
|---|---|---|---|---|
| P23 | scripted, kernel replay claimed by harness | compile, 2.4 s | fail at `SuperReflectionFacts.lean:202` | n/a as submitted |

The failure has the same pattern as P18's. `simpa using
superIterate_step_lt … 0 …` normalizes `superIterate schedule 0 initial`
differently from the goal's `initial`, although the two are definitionally
equal. Using the term directly (tested on the scratch worktree only; the
imported sources are unmodified) makes the whole development compile. The
audit then passes: axioms `propext, Quot.sound`, and the closure (4,196
constants) avoids `contender_5` … `contender_19`.

## What it builds

A third type level: `LiftTransformer := TransformerLift → TransformerLift`.
`promoteLift schedule lift` is one step of the diagonal lift hierarchy.
`superClosure` traverses the schedule *at the level of lifts*, applying that
step at every node. `superIterate` repeats this `family19 n + 1` times,
starting from a self-ranked `diagonalLift`. The result is applied to
large-Veblen ladder reflection, and a final reflection is taken over the whole
family.

## Comparison

It proves `contender_19 < contender_20` for its own number. Traversing the
schedule at the level of lifts gives a lift hierarchy of rank about the
schedule's ordinal, iterated finitely. That is the same class of amplifier as
P22's W-tree rank, which Contender 23 already uses with a rank *above* the
schedule. It keeps Contender 19's language, so it is informally below this
repository's Contenders 20–24. Nothing new is adopted.

# Late arrival: P24

`BusyLean_Contender20_WRank_Hyperreflection.zip` proposes a "Contender 20"
over Contender 19 (base commit `64d31a0`).

| | Definitions | Proofs | Axioms |
|---|---|---|---|
| P24 | compile, 2.0 s | **compile**, 1.2 s | `propext, Quot.sound`; the closure (4,192 constants) avoids `contender_5` … `contender_19` |

Its `treeDiagonalLift schedule rankTree seed` runs the diagonal lift step along
a W-tree rank (`rankTree20 n`, an autonomous notation above the schedule),
seeded with a finite-rank `diagonalLift`. This is P22's idea found
independently, with the same rank shape. It proves `contender_19 <
contender_20` for its own number. It keeps Contender 19's language, so it is
informally below this repository's Contenders 20–24, and Contender 23 already
uses the transfinite-rank hierarchy. Nothing new is adopted; it corroborates
P22.

# Late arrival: P25

`BusyLean_Contender20_Autonomous_WTree_Reflection.zip` proposes a "Contender
20" over Contender 19 (base commit `64d31a0`; validated on a research branch).

| | Definitions | Proofs | Axioms |
|---|---|---|---|
| P25 | compile, 1.8 s | **compile**, 1.0 s | `propext, Quot.sound`; the closure (4,235 constants) avoids `contender_5` … `contender_19` |

## What it builds

A new kind of atom: **finite addresses in a computable W-tree**
(`Ordinal/WTreeLadder.lean`). An address is valid when following it reaches a
subtree, which is decidable by evaluating the tree. `childLt t b a` says `b` is
a valid immediate child of `a`. This relation is well-founded *structurally*:
accessibility of an address is proved by recursion on the subtree it reaches.
No ordinal-notation theory is needed. The tree is `tree12` joined with all
finite autonomous hyper-closures above it. The ladder language of Contender 14
runs over these atoms, with an `F19` orbit as seed and `diagonalLift` as
amplifier.

## Comparison and adoption

It proves `contender_19 < contender_20` for its own number. Its ladder length
is the rank of `tree12`'s hyper-closures, about the W-language's index ordinal.
That is below the Bachmann–Howard and Buchholz-length ladders of Contenders
20–24, so it is informally below them.

The **idea is adopted**, and it is the most consequential one received. If
atoms are addresses in a Lean-defined tree, the ladder length is the tree's
rank, and well-foundedness is free. Contender 25 uses it with the *descendant*
order, which is also structurally well-founded, over trees produced by
Buchholz-style collapsing functions on tree ordinals. Those functions are
defined by plain structural recursion, with no normal forms and no
well-foundedness proofs.

# Late arrival: P26

`BusyLean_Contender20_SecondOrder_Hyperreflection.zip` proposes a "Contender
20" over Contender 19 (base commit `64d31a0`).

| | Definitions | Proofs | Axioms |
|---|---|---|---|
| P26 | compile, 1.6 s | **compile**, 1.7 s | `propext, Quot.sound`; the closure (4,192 constants) avoids `contender_5` … `contender_19` |

Its `diagonalHyperLift` is P17's diagonal rank hierarchy one type level up: it
acts on transformer *lifts* (`HyperLift := TransformerLift → TransformerLift`),
with natural-number rank `family19 n + 1`. It starts from `liftLift`, a lift
staged along the index. Like P23, this is a third-order amplifier with finite
rank, in the class of P22's W-tree-ranked hierarchy that Contender 23 already
uses. It keeps Contender 19's language, so it is informally below Contenders
20–24. Nothing new is adopted.

# Late arrival: P27

`BusyLean_Contender35_Metalanguage.zip` proposes a "Contender 35" over
Contender 34 (base commit `4351340`).

| | Definitions | Proofs | Axioms |
|---|---|---|---|
| P27 | compile | **compile** (worktree at `4351340`) | `propext, Quot.sound`; the closure (5,534 constants) avoids `contender_5` … `contender_34` |

## What it builds

`Ordinal/TreeLanguage4.lean` is System T over naturals and countable trees with
two primitives: `boost : tree → tree` and **`lift : (tree → tree) → tree →
tree`**, an arbitrary language-closure operator. Instantiated with `langLift`,
programs can build tree transformers, close them under the whole lower
language, and keep computing. Contender 34 iterated `langLift` along a tree
*externally*. Here the iteration and any higher-type use of the closure
operator are expressible *inside* the language. `metaBoostT` stacks the
metalanguage along a tree.

## Comparison and adoption

Like Contenders 25–37, it feeds its tree into a ladder as atoms, so by the
truncation argument (article, "A correction: what a ladder sees") its number
grows only through the amplifier. The **tree construction is new and is
adopted**: a first-class closure operator lets programs iterate language
closure themselves. Used through the hierarchy `hier` of Contender 38, the
tree's size counts.

# Retired without import (2026-10-13)

Six archives offered no idea that the repository does not already have, or
that the truncation argument does not make void. They were reviewed, not
imported, and deleted:

| Archive | Target | Idea | Why retired |
|---|---|---|---|
| `Contender25_MetaRound_Reflection` | C24 | atoms from a meta-round tower of `limitAlong` rounds; seed an `F24` orbit | a larger atom order, which a depth-`n` ladder cannot see; orbit seeds are a number-level iteration, subsumed by `hier` |
| `Contender25_SelfHeight_RoundTower` | C24 | `roundTower` of height given by an `F24` orbit | same: a taller atom order plus orbit seed |
| `Contender26_SelfIndexed_CollapsedTree_Reflection` | C25 | `bigTree` at a self-indexed parameter | same: a larger atom tree plus orbit seed |
| `Contender26_W2_Hyperreflection` | C25 | P22's W-ranked lift one type higher (`HyperLift`) | P26 with a W-tree rank; amplifier ranks are dominated by the trees `hier` already runs along |
| `Contender35_SelfIndexed_TransfiniteLanguage` | C34 | `treeStackedTree` at a self-indexed depth, orbit seed | same: a larger atom tree plus orbit seed |
| `Contender38_MetaLanguage` | C37 | System T with `langLift` as a first-class constant over `boost31` and a seed; self-rebased tower | the same idea as P27 (which is parametric in its primitives and was built); its own extra, the diagonal `t ↦ metaStack t t t`, is a tree-level diagonal of the kind already in `bootT`/`stackOver`; kernel check never run |

# Retired without import (2026-10-13, second batch)

| Archive | Target | Idea | Why retired |
|---|---|---|---|
| `Contender42_ReaderTree_HyperHierarchy` | C41 | `hyperHier`: iterate the hierarchy-forming operator `g ↦ hier g T` along a second tree (here `succ T`) | a hierarchy along roughly `T·2`. Ordinal arithmetic on the index adds nothing: the trees `hier` runs along (Contender 38 on) are already closed under such operations, and later contenders' trees dwarf it |
| `Contender42_StratifiedSemanticRayo` | C41 | a first-order language with arithmetic, iteration, an oracle, and rank-lowering semantic reflection; diagonal over ranks ≤ `n` | number-level reflection over a weak base language, the pattern of Contenders 6–14 over much stronger languages (System F, Fω, ladders); no kernel replay was run |
| `Contender25_OmegaRound_Closure` (third batch) | C24 | atoms from the ω-limit of Contender 24's round towers (`WFO.sigma omegaIndex roundTower`) and `limitAlong` above it; `F24` orbit seed | a larger atom order, which a depth-`n` ladder cannot see; the orbit seed is a number-level iteration subsumed by `hier` |

# Retired without import (2026-10-13, fourth batch)

| Archive | Target | Idea | Why retired |
|---|---|---|---|
| `Contender50-ImpredicativeResourceReflection` | C49 | reflection values become the resource bounds (program depths, rounds, collapse parameters) of the next stage; two passes; successor-based final hierarchy | a number-level diagonal (composition). Contender 54's programs already build trees, reflect over them and iterate; not kernel-checked |
| `Contender48_CertifiedDescent` | C47 | a first-order programming model whose recursion must descend a certificate tree | weaker than tree recursion at all types in FT2 and PTL; not kernel-checked |
| `Contender54_Birkhoff_Sperner_Tower` | C53 | iterated order-ideal lattices of finite posets (Dedekind-number growth), iterated `family53 n + 1` times | a finite combinatorial amplifier of tower-like growth, far below the hierarchy machinery; not kernel-checked |
| `Contender54_SemanticWorldClosure` | C53 | iterate a pair (number oracle, tree): jumps with the current oracle enlarge the tree, then reflection over it gives the next oracle | number oracles change trees only by finite amounts; the tree iteration is covered by Θ/Ψ/`iterLevel` and the reflection by Contender 54's `reflT` primitive; not kernel-checked |
| `Contender54_TILED` | C53 | large elimination of a tree into `Type` (leaf `Nat`, successor endomorphisms, limit Π) with canonical iterators, observed as numbers | the pattern of Contender 31's transfinite types `AT` (there over universes), here over `Nat`. It gives about ε-type speed-ups along the tree, which the trees already absorb. It was CI-checked, but the idea is already in the repository |

# Retired without import (2026-10-13, fifth batch)

All three are finite combinatorial amplifiers: at most an `N`-fold iteration of
an elementary function, with tower-of-exponentials growth. That is negligible
next to one application of the predecessor family they are seeded with, the
same category as the retired `Contender54_Birkhoff_Sperner_Tower`. None was
kernel-checked.

| Archive | Target | Idea | Why retired |
|---|---|---|---|
| `Contender54_YonedaDedekind` | C53 | iterated "Yoneda–Dedekind" completion `Y(P) = P ⊔ Idl(P)` of finite posets from a Boolean lattice, `N` times (the closed term is `F54 42`, not `F54 (F54 42)`) | Dedekind-number, tower-type growth; a finite amplifier |
| `Contender55_Plethystic_FreeMonad_Reactor` | C54 | polynomial containers with plethysm, jets, feedback arities and bounded free-monad trees, iterated `N + 1` times | primitive-recursive-style growth; a finite amplifier |
| `Contender60_SelfWreath` | C59 | iterated self-wreath products `G ↦ G^G ⋊ Sym(G)`, order `a ↦ a^a·a!`, `N + 1` steps | an exponential tower of height about `N`; a finite amplifier |
