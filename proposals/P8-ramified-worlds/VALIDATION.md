# Validation record

## Actually completed in this environment

1. Inspected the upstream README, proposal review, core P5 definitions and
   proofs, Contender 6 definitions, reflection definitions and facts,
   comparison module, and audit design through the GitHub connector.
2. Developed the complete mathematical comparison and separation arguments
   in the article. No claimed ordinal calibration is used.
3. Ran the Python reference tests: **9 test methods passed**. The tests include
   144 small-value semantic witness cases (36 child indices times 4 scores),
   exact type/depth checks, oracle independence, and cast behavior.
4. Performed a lexical delimiter-balance check of the Lean source files.
5. Compiled the LaTeX article to PDF with pdfLaTeX and rendered the pages for
   layout inspection.

## Not completed

- Lean elaboration and kernel checking of the supplied new source.
- A successful `#print axioms` run for the new declarations.
- Execution of the new transitive dependency/axiom audit.
- Measurement or certification of the definition/proof contest budgets.
- Evaluation of any complete contender (neither intended nor attempted).
- Exact pointwise comparisons with each of P1, P2, P3, and P4.

No `lean` or `lake` executable is installed in this environment. The actual
`check_lean.py` attempt records `status: unavailable`, with no executed build
phases, in `audit/lean-validation.json`. Attempts to fetch a compiler did not
produce a usable installation. No build-success log or timing is invented.

The source is intended as a complete formalization and contains no `sorry`,
`admit`, custom `axiom`, `native_decide`, or noncomputable/partial replacement
for the mathematical number. However, source inspection cannot establish
that it compiles. Elaboration or library-interface fixes may be needed before
it becomes a kernel-validated contest submission.

The article's theorems are mathematical claims with explicit proofs. The
statement that their supplied Lean encodings have been checked would be a
separate empirical claim; it is not made here.

## Scope of the reference tests

`tests/reference.py` models the new atom/application fragment used by the
comparison certificate. It deliberately does not enumerate the complete
reflected W-language. Its numerical safety limits are test-harness limits,
not truncations in the Lean or mathematical definition. Passing these tests
is useful independent evidence for the exact witness, not a formal proof.

## Revalidation

Run `python3 scripts/check_lean.py` with the pinned toolchain installed. The
script stops on a build failure, timeout, or audit error. Preserve the logs
when repairing any source issue. After successful compilation, inspect the
proof statements and ensure no repair silently changes exact casts, the
seed, the index, the enumeration, or the 42-fold bound.
