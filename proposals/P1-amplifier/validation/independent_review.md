# Independent review: incumbent fidelity and hierarchy interpretation

This review covers the exact computational port in `BigNumber/BaselineDefs.lean`,
the selected-maximum proof in `BigNumber/Baseline.lean`, and the structural tree
amplifier in `BigNumber/AmplifierDefs.lean` and `BigNumber/Amplifier.lean`.

## 1. Exact computational scope of the incumbent port

The upstream source is `Contender.v` in
<https://github.com/codyroux/name-the-biggest-number>.
The supplied source snapshot has SHA-256
`a809222145e3063b742af7f35e4e6ec41ca37d60ef32140958a5f09ccd21d04b`.
The supplied rules snapshot has SHA-256
`a20f2a1c951ce7558e771bb935c849bc391ec22075cd97ca3765b52e7ec7e09e`.
The repository's captured revision and snapshot files are the authoritative
provenance; these hashes distinguish the reviewed bytes from later updates.

The Lean port preserves the following details, each of which can change the
number if simplified incorrectly.

| Upstream feature | Lean treatment |
| --- | --- |
| Types are natural numbers and arrows, with natural-number type depth 1 | `Ty`, `typeDepth` |
| Variables have depth `x + 2` | `natDepth`, `termDepth` |
| Both lambda type annotations contribute to term depth | `termDepth` |
| Variable zero selects the final environment element | `lookup` uses `length - (n + 1)` after a bounds test |
| Lambdas prepend a value, so zero denotes the outermost binder | `interpTerm` and nested-lambda reduction tests |
| Unbound variables interpret as a natural-number zero | `interpTerm` variable case |
| All raw terms, including ill-typed terms, are admitted | `termsUpTo` is not filtered by a typing judgment |
| A natural-valued application head produces a natural-number zero | `interpTerm` application case |
| A lambda casts its body result to its annotated codomain | `interpTerm` lambda case |
| Casts at unequal types produce structural default values | `error`, `castError`, `castImpl` |
| Casts at equal arrow types recursively transform arguments/results | `castImpl` uses the forward/backward pair exactly as upstream |
| Natural recursion takes zero value, predecessor-sensitive step, then input | The `Nat.rec` interpretation has order `R → (Nat → R → R) → Nat → R` |
| A final function-valued result contributes zero to the score | `eval` |
| Cartesian products have their left argument as outer loop | `listProd` |
| Variables, lambdas, applications, zero, successor, recursors occur in that order | `termsUpTo` |
| The previous winner survives a tie | `maxBy` tests strict inequality |
| The initial winner is the zero term with score zero | `largestOfDepth` |
| The incumbent is the selected winner's value at depth 42 | `contender_5` |

The alternate numerical maximum `envelope n` is proved equal to that selected
winner's value using a generic invariant. The theorem does not rely on a typing
restriction, a reification theorem, or evaluating the depth-42 enumeration.

The cross-language connection is a reviewed computational translation. The Lean
kernel checks the port and its comparison theorems. It does not import a Coq
kernel proof that a Coq expression and a Lean expression denote the same natural
number. This trust boundary should remain explicit.

The optional `BigNumber/BaselineSmoke.lean` executable test produces:

| Depth | Number of types | Number of raw terms | Maximum value |
| ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 0 |
| 1 | 1 | 2 | 0 |
| 2 | 2 | 10 | 1 |
| 3 | 5 | 146 | 2 |
| 4 | 26 | 24,976 | 3 |

Its selected representatives are zero, zero, successor zero, two successors,
and three successors. Separate closed `rfl` proofs distinguish both reversed
variable indices and check malformed applications, codomain mismatch defaults,
and natural recursion with a nonzero initial value.

## 2. Axiom audit

The computational definitions already used no axioms. During proof review,
several standard-library maximum and list-membership lemmas were found to carry
`propext` transitively. They were replaced by direct arithmetic and inductive
proofs. The final audit reports no axioms for each of:

- `BigNumber.Baseline.contender_5`
- `BigNumber.Baseline.envelope`
- `BigNumber.Baseline.eval_maxBy`
- `BigNumber.Baseline.contender_5_eq_envelope`
- `BigNumber.Baseline.initial_le_foldMax`
- `BigNumber.Baseline.envelope_bound`

The port therefore does not inherit the upstream reification development's
functional-extensionality import. There is no use of `sorry`, `axiom`,
`Classical.choice`, `funext`, or `propext` in these audited dependencies.
Measured clean-build timings and complete audit logs are supplied separately.

## 3. Why the Veblen names are heuristic

The tree syntax and its evaluator are fully defined. An identification with a
standard ordinal-indexed fast-growing hierarchy is not part of the result.
There is a concrete obstruction to treating `veblenTree` as a function only of
the ordinary ordinal value of its first tree argument.

For this explanation, equip trees with the ordinal **valuation**

\[
\rho(\mathsf{zero})=0,\qquad
\rho(\mathsf{succ}(a))=\rho(a)+1,\qquad
\rho(\mathsf{limit}(f))=\sup_n\rho(f(n)).
\]

This is the usual interpretation of zero, successor, and limit notation; it is
not the strict well-founded height of the underlying W-type. Under this
valuation, grafting implements addition in the second argument and
`omegaPower a` has value \(\omega^{\rho(a)}\). Those claims follow by structural
induction and the continuity of ordinal addition and exponentiation. They are
explanatory ordinary mathematics here, not imported Lean ordinal theorems.

Now let \(z=\mathsf{zero}\) and
\(q=\mathsf{limit}(n\mapsto z)\). Both have value zero. Nevertheless:

1. `veblenTree zero zero = omegaPower zero`, whose value is 1.
2. `veblenTree q zero` is the common fixed-point closure at zero of the constant
   family \(\Omega(a)=\mathsf{omegaPower}(a)\).

For the constant family, `prefixApply fs k a` is exactly \(\Omega^{[k]}(a)\),
and a direct induction gives

\[
\mathsf{sweep}(fs,k,a)
 =\Omega^{[k(k+1)/2]}(a).
\]

Thus the limit defining `veblenTree q zero` selects the unbounded iteration
counts \((n+1)(n+2)/2\). Starting at zero, their ordinal values have supremum
\(\varepsilon_0\), the least fixed point of ordinal exponentiation by omega.
Consequently these two trees with equal index value zero produce output values
1 and \(\varepsilon_0\), respectively.

This rules out the unconditional claim

\[
\rho(\mathsf{veblenTree}(t,a))
 =\varphi_{\rho(t)}(\rho(a))
\]

for arbitrary raw trees. A separate normal-form/cofinality development would be
needed for an exact calibration on an appropriate subclass. The term
**Veblen-inspired** is accurate; an assertion of a proved Veblen ordinal, a
proved \(\Gamma_0\) seed, or a particular standard fast-growing hierarchy value
would go beyond the present results.

## 4. Amplifier correctness independent of calibration

The amplifier uses structurally terminating recursion on `Tree` and `Nat`.
Recursive calls through a limit node go to its immediate child `f n`.
The `Level` family creates only finitely many function-space levels at any
particular natural-number index. Evaluation of a large natural parameter need
not occur during type checking of its symbolic definition.

The central identity is the pointwise substitution law

\[
F_b(\mathsf{graft}(a,t),n)=F_{F_b(a,\,\cdot\,)}(t,n).
\]

Its Lean proof uses pointwise iteration congruence and requires no function
extensionality. The lower-bound proof assumes inflationarity of the base;
it does not silently assume monotonicity in the input or in an ordinal index.
Successor evaluation exposes its first application, and every later application
can only increase the current argument. This proves \(F_b(t,n)\ge b(n)\).

The quantitative argument also checks out. If \(b(n)\ge n+1\), then each of the
64 iterations after the first one in a successor evaluation at 64 adds at least
one. Graft substitution transfers this gain to `advance`. Writing
\(s(a)=F_b(a,64)\), one obtains

\[
s(\mathsf{advance}(a))\ge s(a)+64.
\]

The **final submitted definition** uses the tower function

\[
T(0)=1,\qquad T(n+1)=2^{T(n)}
\]

and performs exactly \(T(s(a)+1)\) advances during a stage. That iteration count
is frozen from the initial tree of the stage. It is not recomputed after each
advance. The score inside `advance` is still recomputed from its current tree
when selecting its higher-type seed, as its separate definition specifies.
The resulting stronger raw bound is

\[
s(\mathsf{stage}(a))
 \ge s(a)+64T(s(a)+1)
 \ge T(s(a)+1).
\]

`tower2_lower` proves \(n+1\le T(n)\), and `tower2_mono` proves monotonicity of
\(T\). Define the numerical feedback sequence

\[
\theta(s,0)=s,\qquad
\theta(s,k+1)=T(\theta(s,k)+1).
\]

Induction along the ladder gives

\[
\theta(s_0,k)\le s(\mathsf{ladder}(k)),\qquad
\theta(s_0,s_0)\le\mathsf{candidate}(b),
\qquad s_0=\mathsf{seedScore}(b).
\]

These are the formal `ladder_tower` and `candidate_tower` theorems. The proof
uses monotonicity of the elementary numerical function \(T\), not an assumed
monotonicity of the tree evaluator.

The previous exponential bound remains a valid weaker consequence: the final
stage performs at least \(s(a)+1\) advances, so

\[
s(\mathsf{stage}(a))+1\ge65\bigl(s(a)+1\bigr),
\]

and therefore

\[
\mathsf{candidate}(b)+1
 \ge65^{s_0}(s_0+1),\qquad s_0=\mathsf{seedScore}(b).
\]

All these guarantees remain valid regardless of how the Veblen-inspired
constructors might eventually be calibrated by an ordinal interpretation.
The separately proved `fast_at_zero` identity, \(F_b(a,0)=b(0)\) for every tree
\(a\), also makes clear why a syntactically large tree alone is not a proof of
a large score at every possible input.

## 5. Final incumbent comparison and tower guarantee

The final `BigNumber/CandidateDefs.lean` defines the submitted closed natural
number by

```lean
def contender_6 : Nat := Amplifier.candidate base
```

The definition uses the general envelope-based function `base`; it does not
refer to the earlier `contender_5` constant. The comparison in
`BigNumber/Candidate.lean` separately names that incumbent in its theorem
statements.

Let \(C=\mathsf{contender\_5}=E(42)\). The inclusive prefix sum in the base
contains \(E(42)\) when evaluated at 64, so the reviewed proof establishes

\[
C<b(64)\le s_0,
\qquad
C<b(64)\le\mathsf{contender\_6}.
\]

Only nonnegativity of the other envelope values is needed here; monotonicity
of the envelope function is not presumed. This proves the strict contest
comparison, `contender_5_lt_contender_6`.

`towerFeedback_seed_mono` and `towerFeedback_rounds_mono` prove that
\(\theta\) is nondecreasing separately in its initial seed and its round
count. Since \(C+1\le s_0\), the final direct incumbent bound is

\[
\boxed{\theta(C+1,C+1)\le\mathsf{contender\_6}}.
\]

The theorem name is `contender_6_tower_bound`. Its companion
`contender_6_seed_tower_bound` uses the stronger parameters \(s_0,s_0\).
Both statements refer directly to the named submitted number.

The earlier quantitative comparison is retained as

\[
65^{C+1}(C+2)\le\mathsf{contender\_6}+1.
\]

In the Lean declaration `contender_6_exponential_bound`, the right side is
spelled `Amplifier.candidate base + 1`. This expression is definitionally the
same as `contender_6 + 1`; the spelling keeps elaboration symbolic and avoids
unproductive unfolding of the enormous closed alias during arithmetic
elaboration. It does not weaken or change the mathematical theorem.

An independent final audit of the compiled modules reports no axioms for all
eight of the following constants:

- `BigNumber.contender_6`
- `BigNumber.contender_5_lt_contender_6`
- `BigNumber.contender_6_exponential_bound`
- `BigNumber.contender_6_tower_bound`
- `BigNumber.contender_6_seed_tower_bound`
- `BigNumber.Amplifier.candidate_tower`
- `BigNumber.Amplifier.fast_graft`
- `BigNumber.Amplifier.fast_at_zero`

The final proof mathematics was reviewed against the stronger stage
definition, including the frozen iteration count, the two separate monotonicity
arguments for \(\theta\), and both incumbent substitutions. No mathematical
issue was found. The construction is a concrete verified entry with a large
certified margin; no optimality claim over all entries that could fit a
particular machine's resource limits is made.
