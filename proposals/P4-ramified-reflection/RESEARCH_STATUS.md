# Research and verification status

This document separates mathematical proofs, proposed formal source, and
observed machine validation. Do not describe this package as kernel-verified
or timing-qualified unless the acceptance gates have actually succeeded.

## Mathematical results

| Result | Article | Lean source | Observed verification |
|---|---|---|---|
| Fidelity of legacy numerical semantics | Proposition 2.2 | Computational port | Small instances only; no Coq-to-Lean certificate |
| Exact finite depth coverage | Lemma 3.1 | Only required constructor-occurrence lemmas | Small depths checked |
| Fixed-language diagonal escape | Theorem 4.1 | Not formalized | Numerical-encoding/inequality tests only |
| Constructive stage totality | Theorem 5.2 | Explicit recursor definitions | Compiler not run |
| Visible-child separation | Theorem 5.3 | `reflect_child_lt` | Proposed proof, uncompiled |
| 2^28 branch visibility at input 64 | Corollary 5.4 | Not formalized | Boundary syntax-depth tests |
| Uniform exponential lower bound | Lemma 6.1 | Not formalized | Power-of-two term tested on small inputs |
| Oracle-fed iteration | Theorem 6.3 | Not formalized | Witness semantics tested on simple oracles |
| Supremum/collapse commutation | Lemma 7.1 | Not formalized | Finite observations only |
| Adjacent higher-type levels | Proposition 7.2 | Only `high_zero` | Finite observations only |
| Feedback stage comparisons | Theorem 8.2 | `reflect_boost_lt`, `boost_feedback_lt` | Proposed proofs, uncompiled |
| Grand-index comparisons | Theorem 8.4 | Unary-index versions in `Proofs.lean` | Proposed proofs, uncompiled |
| C5 strictly below every stage at 64 | Theorem 9.1 | `contender_5_lt_reflect` | Proposed proof, uncompiled |
| C5 strictly below entry | Corollary 9.2 | `contender_5_lt_contender_6` | Proposed proof, uncompiled |
| E_(C5+1)(64) strictly below entry | Theorem 9.3 | Not formalized | Mathematical proof only |

## Actual runs

`validation/python_tests.json` records 62,065 passing assertions. No giant
stage, baseline at depth 42, or entry was evaluated. Resource guards in the
Python model reject excessive inputs and never substitute approximate values.

`validation/lean_validation.json` records that no Lean compiler was available.
The lexical source screen passed. That screen is not a transitive axiom audit,
a Lean parser, a termination checker, or a proof checker.

The PDF was compiled from the supplied TeX and visually reviewed as rendered
page images. Its build and inspection records are separate from the Lean
validation report.

## Required before contest acceptance

1. Compile the exact definition dependency closure on the pinned toolchain.
2. Repair any elaboration or API problems while preserving the mathematical
   definitions and comparison target.
3. Compile the comparison proof and obtain empty transitive axiom reports.
4. Measure the disclosed 15-second definition and 60-second proof phases.
5. Preserve compiler version, machine information, logs, and final checksums.

No claim is made that these steps have already succeeded. None of the missing
machine evidence is a reason to retract the explicit mathematical construction
or its paper proofs; it is a reason not to label the source as certified.

## Scope of novelty and mathematical interpretation

Finite maxima over total typed languages are inherited from Contender 5.
The W-recursive language extension, tree-indexed numerical oracle reflection,
higher-type feedback construction, and precise witness-based separation are
proposed here. A comprehensive novelty/prior-art search was not completed,
and no proof-theoretic ordinal classification is asserted.

General higher-type identities in the article are expressed extensionally.
The supplied strict comparison path does not assume functional extensionality;
the relevant general extensional identities are not among its dependencies.
The tree type is an inductive W-type, not a quotient of ordinal notations.
