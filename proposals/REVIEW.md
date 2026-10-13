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
