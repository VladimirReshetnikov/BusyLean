# Validation status

## What was actually executed

- The Python reference/test suite passed. It checks the original enumerator at
  depths 0 through 4, rank certificates, 480 generic compiler environments,
  selected tree branches and same-type casts, a nonmonotone-program example,
  and small bounded tower properties. See `evidence/python_tests.json`.
- The comparison term has rank 17; its intermediate tree and number terms have
  ranks 14 and 16. A recursively checked syntax certificate is included.
- Depth 4 contains 147,129 raw terms. These were enumerated and checked for rank
  and membership properties, **not all interpreted**.
- All three vendored Lean files have exactly the expected Git blob SHA-1.
- A lexical source audit passed. It is not a semantic/transitive audit.
- The article was compiled to PDF; PDF validation is recorded separately.

## What was NOT executed

**There is no Lean executable in this environment. The new Lean definitions,
proofs, smoke checks, axiom commands, and dependency-closure commands have not
been run through Lean.** Toolchain download attempts were unsuccessful. The
provided source is a proof implementation proposal, not a kernel-certified
contest entry. No claim of successful elaboration is made.

The article supplies full mathematical arguments. Their translation into Lean
may require elaboration repairs. The most delicate portions are same-type
W-cast simplification, dependent interpreter reduction, and rank-membership
proofs. None contains intentional proof holes or admitted axioms.

The 15-second definition budget and 60-second proof budget are **unmeasured**.
The audit permits only `propext` and `Quot.sound`, but its result is not known.
The optional full-repository integration file is also uncompiled.

## Reproduction

From this package root, with Python 3.10+:

```sh
python3 python/test_reference.py
python3 scripts/source_audit.py
python3 scripts/check_lean.py
```

The last command requires Lean **4.34.0** on PATH; an explicit executable can be
supplied with `--lean /path/to/lean`. It exits 2 when unavailable, never treating
absence as success. It creates a clean local build directory, checks definitions
before proofs, then runs dependency/axiom audits and tiny smoke checks. The audit
phase is charged to the proof budget. No network or Mathlib is needed after the
Lean toolchain is installed. The script and all new Lean files themselves need
external validation; the script cannot repair Lean errors.

Never evaluate `contender_7`, `finalNumber`, or a concrete semantic-library
maximum, including at input zero. The smallest reflection budget is already 17.

## Comparison coverage

The paper proves a direct comparison against the pinned current Contender 6.
An optional integration file chains the repository's existing C5 and P5
comparisons. This package does not provide separate exact comparisons with
archived proposals P1-P4. Their ranking below P5 in the upstream review uses
informal ordinal estimates; those estimates are not imported as theorems here.
