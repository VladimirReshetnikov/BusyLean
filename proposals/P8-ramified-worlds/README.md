# BusyLean: Contender 7 by ramified semantic worlds

This research package proposes a computable-in-principle number that exceeds
BusyLean's incumbent Contender 6 by an explicit, very large margin.

Let `A(x)` be `x` iterations of `u ↦ 2^u`, starting at `x`. The article proves

    A^[42](BusyLean.contender_6) < BusyLean.V7.contender_7.

The proposal reflects **whole lower-world tree-recursion operators** with
arbitrary seed and tree arguments, not just the preceding named number.
It generates a new program-defined tree index, ramifies world construction
along the preceding world's index, and iterates that operation 42 times.

## Validation status — read first

The 16-page mathematical article and its PDF are complete. The independent
Python certificate tests pass (nine test methods). The Lean definitions and
comparison-proof source contain no placeholders, but **have not been compiled
or kernel-checked in the authoring environment**. No Lean compiler was
installed. The axiom/dependency audit and the 15-second/60-second contest
budgets are therefore **not certified**. This is a research proposal with
uncompiled formalization source, not an already accepted contest entry.
See `VALIDATION.md` and `audit/lean-validation.json`.

Never evaluate `contender_7`, `levels 42`, a complete high-depth program
maximum, or any inherited contender. Checking a definition is not evaluating
its value.

## Contents

- `article/ramified_semantic_worlds.tex` and `.pdf`: definitions, proofs,
  scope, limitations, source audit, and research directions.
- `lean/BusyLeanNext/Definitions.lean`: proposed construction and witnesses.
- `lean/BusyLeanNext/Proofs.lean`: formalization source for the comparisons,
  finite-enumeration facts, numerical separation, and tree-index separation.
- `lean/test/Audit.lean`: axiom and transitive dependency audit tooling.
- `lean/test/Smoke.lean`: small arithmetic checks only.
- `tests/`: independent typed evaluator for the small comparison-witness
  fragment; not an implementation of the complete reflected language.
- `scripts/check_lean.py`: clean, timed build and audit driver.
- `scripts/build_article.sh`: reproducible PDF compilation.
- `audit/`: actual test output, explicit unavailable-compiler record,
  source provenance, and the depth-7 witness certificate.

## Reproduce

Install the repository's pinned Lean 4.34.0 toolchain and Python 3.10 or newer.
From this package's root:

```bash
python3 scripts/check_lean.py
python3 -m unittest discover -s tests -v
bash scripts/build_article.sh
```

The Lean project fetches BusyLean at commit
`86b360648163f0249eab79539438b6a83dfe8215`. Dependency retrieval is outside the
contest timing. The definition build includes all imported non-core modules.
The proof build reuses those just-checked definitions. Audit and smoke checks
run separately. A missing toolchain or timeout is a failure/unavailable
result, never a pass.

The main Lean declarations, under `BusyLean.V7`, are:

```lean
def contender_7 : Nat := score (levels 42) 42

theorem towerOrbit_contender6_lt_contender7 :
    towerOrbit BusyLean.contender_6 42 < contender_7

theorem contender_6_lt_contender_7 :
    BusyLean.contender_6 < contender_7
```

The final number is not a literal `towerOrbit` application to the predecessor;
that expression is only a lower bound in the proof.

## Comparison scope

The exact mathematical comparison is against the incumbent Contender 6.
Upstream's existing theorems then give strict comparisons with P5 and the
faithful Contender 5 port. No exact, fixed-input theorem comparing each
separate P1–P4 proposal is claimed here. Their informal ordinal ranking is
not used as a proof.

The construction reuses the previous **generic** runner, program-generated
index, and P5 seed family. It does not claim independence from all predecessor
machinery. The included audit is intended to verify that the *definition's*
transitive closure excludes the named incumbent, its final-family wrapper,
and the proposal-level named contender constants.

See `INTEGRATION.md` for repository integration without replacing existing
files or changing the old contender.
