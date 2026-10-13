# Validation boundary

## Established in this run

- The three vendored source files match the pinned Git blob hashes exactly.
- The new definitions were inspected for structural recursion and explicit
  dependency order; the article gives mathematical proofs of the stated bounds.
- The independent Python interpreter passed 1,830 assertions, including 976
  exact certificate evaluations, enumeration counts through depth 4, finite
  extensional W-cast checks, and 48 small reflected-maximum cases.
- A lexical source scan found no intentional `sorry`, `admit`, custom axiom,
  `noncomputable`, `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
  `native_decide` in the new Lean modules. It found no direct use of the three
  forbidden prior-winner names in the new definitions.
- The article PDF was compiled and visually inspected (see PDF receipt).

## NOT established in this run

- New Lean code successfully elaborates, type-checks, or compiles.
- The kernel accepts the 84 new theorem scripts.
- The final transitive axiom/dependency closure passes the supplied audit.
- The definition/proof phases meet the 15/60-second contest budgets.
- A semantic correspondence theorem between Python and Lean.
- An exact comparison against the separate P1-P4 proposal constants.
- An ordinal calibration or a literature-wide novelty/optimality claim.

The local environment lacked Lean/lake. Git/toolchain retrieval was unavailable,
and a search for an available compiler integration did not provide one. No
successful build, kernel audit, or timing has been fabricated. On a machine
with Lean 4.34.0, run scripts/check.py and use its actual output to update this
ledger. Lexical scans are not dependency-closure checks, and numerical tests
are not formal proofs.
