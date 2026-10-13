# Research notes: Contender 20

## 1. Design objective

At the audited base revision, Contender 19 already combines a large-Veblen
universe ladder with a high-rank W-tree hyperreflection amplifier. A meaningful
successor therefore needed both an exact numerical comparison and a new
structural idea. The proposal introduces a non-linear, W-tree-indexed universe
hierarchy and separately strengthens the seed from one repeated previous family
to a visible orbit of `F19`.

## 2. Alternatives considered

### A. Successor or fixed postcomposition

Definitions such as `contender_19 + 1`, `F19 contender_19`, or a fixed number of
extra `F19` iterations would be valid but mathematically uninteresting. They do
not add reusable formal infrastructure, and their gap is weaker than the
self-length orbit lower bound proved here.

### B. Another explicit linear ordinal notation system

One route was to add a constructor resembling a collapsing function above the
large-Veblen terms. This would require a new normal-form discipline and a
substantial accessibility proof. Without a complete ordinal assignment, the
resulting notation could also invite misleading benchmark claims. The chosen
W-tree construction instead reuses the repository's own autonomous tree
language while obtaining well-foundedness directly by structural recursion.

### C. Transitive ancestor relation

A natural atom order is strict descendant rather than immediate child. That
would let a parent universe directly see every proper descendant. The immediate
relation was chosen because:

1. its accessibility proof follows the exact `WTree` recursion with minimal
   auxiliary machinery;
2. deeper descendants remain available through nested child universes;
3. it avoids a new transitive-closure enumerator in the first proposal;
4. `FL.wfUniv` requires well-foundedness, not linearity or transitivity.

A certified transitive variant remains a high-priority follow-up.

### D. Seed only, with no new language

An orbit-seeded copy of the existing large-Veblen reflector would already beat
Contender 19. It was rejected as incomplete: the W-tree language contributes a
separate theorem (`avalue_lt_F20`) and a reusable generic construction rather
than relying solely on a larger seed.

## 3. Exact proof architecture

The proof deliberately avoids monotonicity assumptions.

1. `input_lt_F19 x` gives `x < F19 x` for every `x`.
2. Therefore one more structurally defined `iterateF19` step is strictly
   larger, regardless of whether `F19` is known to be monotone.
3. `reflectAFamily` is progressive because it adds `n + 1` above the maximum
   of all visible oracle coordinates and program values.
4. Generic `diagonalLift_preservesProgressive` gives
   `orbit19 i n < F20 n` for every `i <= n`.
5. Coordinate zero is definitionally `F19 (F19 n)`, so the previous family is
   beaten pointwise.
6. Two applications of `input_lt_F19` show `n < family19 n`; transitivity makes
   `F20` inflationary.
7. At `n = 42`, this yields `contender_19 < F20 42`; inflationarity at
   `F20 42` yields `F20 42 < contender_20`.
8. At `i = n = F20 42`, the same generic orbit theorem yields the stronger
   self-length `F19`-orbit lower bound.

## 4. Computability boundary

The construction is computable in principle because every new definition is
structural and every reflected list is finite at each input. The object-language
normalizer is justified by a constructive strong-normalization theorem over the
well-founded atom relation. No attempt should be made to evaluate the contest
input; formal symbolic comparison is the intended method.

## 5. Exact claims versus heuristic interpretation

### Kernel-checked

- `childLt_wf` and `wLevel_wf`.
- `sn_erase_wlevel`.
- all one-step reflection bounds.
- `orbit19_lt_F20`.
- `avalue_lt_F20`.
- `contender_19_lt_contender_20`.
- `long_F19_orbit_lt_contender_20`.
- the axiom and dependency reports recorded in `validation/`.

### Not established

- a standard named order type for `autonomousUniverseTree`;
- an order embedding from the large-Veblen atom system into `WLevel`;
- strict proof-theoretic language-strength domination over Contender 19;
- monotonicity of `F19` or `F20`;
- any feasible numerical evaluation, decimal expansion, or residue of the
  contest value.

## 6. Review-sensitive points

- `WLevel` is all finite paths, including invalid ones. Invalid paths have no
  predecessors and are therefore harmless in the semantic instance; the finite
  term enumerator filters to valid paths.
- `childLt` is the immediate valid-child relation. It is not claimed to be a
  linear order or a transitive ordinal notation.
- The exact comparison uses the `F19` function but the transitive closure of
  the closed `contender_20` definition excludes the named previous contender
  constants. This matches the repository's existing functional-family style.
- The timing budget is measured incrementally after building
  `BusyLean.Comparison19`, not from a completely empty dependency cache.
- The GitHub Actions times are environment-dependent engineering evidence;
  theorem validity is independent of those times.

## 7. Recommended next theorem

The most valuable next formal result would be an order-preserving embedding
from normal large-Veblen terms into a transitive W-tree address order, followed
by a semantic embedding of the corresponding universe languages. That would
turn the present heuristic language-strength motivation into an exact theorem
while preserving the already certified numerical domination.
