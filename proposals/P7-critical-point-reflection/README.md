# BusyLean Contender 7: Autonomous Critical-Point Reflection

This archive proposes a new closed Lean natural number, `BusyLean.contender_7`, for the BusyLean repository.  The construction is deliberately split into two layers:

1. **A conservative, machine-checked domination spine.**  Branch zero is definitionally the complete reflection schedule used by Contender 6.  Forty-two recursively guarded branch extensions and one outer root give an explicit strict chain from Contender 6 to Contender 7.
2. **An aggressive autonomous payload.**  A transparent Brouwer-tree syntax supports ordinal-shaped addition, multiplication, exponentiation, fixed-point derivatives, a finite critical-function hierarchy, a diagonal common-critical-point closure, and forty-two higher-derivative levels.  The level-41 payload is formally proved to occur below the final number.

The exact definition is:

```lean
def contender7Index : WTree Nat := .node contender7Branch

def contender7Family (n : Nat) : Nat :=
  stage p5Family contender7Index n

def contender_7 : Nat := contender7Family 42
```

where `contender7Branch 0 = index` and each successor branch contains both the preceding guarded branch and the next autonomous payload.

## What is formally proved

The supplied Lean development proves, among other statements:

```lean
BusyLean.contender_6 < BusyLean.contender_7
BusyLean.contender_5 < BusyLean.contender_7
```

It also proves every guarded branch is below its successor, the forty-two-step chain from the old index to branch 42, branch 42 below the outer root, and the level-41 payload below the final number.  These results do **not** depend on an informal ordinal calibration.

## Computability status

`contender_7` is a closed term of type `Nat`.  Its recursion is structural on `Nat`, the transparent tree syntax `OTree`, or the inherited well-founded `WTree`.  There is no halting oracle, unbounded minimization over an undecidable predicate, `partial`, `unsafe`, `noncomputable`, `extern`, custom axiom, `sorry`, or `Classical.choice` in the submitted construction.  The value is computable in principle but intentionally infeasible to normalize at input 42.

## Verification result

The clean CI run at repository commit

```text
c01efa921d20fcb1d731329ef5582fd16c933fcb
```

reported:

```text
definitions: 1.45 s (budget 15 s)
proofs:      2.15 s (budget 60 s)
PASS: 17 declarations audited; axioms within ['Quot.sound', 'propext']
```

The new definition and all principal Contender 7 theorems reported `propext` only.  The transitive dependency closure of `contender_7` contained 575 constants and avoided all eight specifically forbidden previous-winner names.  The feasible sanity check evaluated `contender7Family 0` to `4`; the final input 42 was not evaluated.

Toolchain:

```text
Lean 4.34.0, kernel commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b
Lake 5.0.0-src+293d5d0
Ubuntu 24.04 GitHub-hosted runner
```

## Archive layout

- `article/contender7_autonomous_reflection.tex` - full research article.
- `article/contender7_autonomous_reflection.pdf` - compiled 14-page article.
- `lean/` - repository overlay containing the exact Lean sources, test, checker, and CI workflow.
- `integration/contender7.patch` - unified patch against BusyLean main commit `86b360648163f0249eab79539438b6a83dfe8215`.
- `verification/contender7-check.log` - captured clean checker output.
- `verification/toolchain.txt` - exact verified revision and toolchain.
- `verification/latex-build.log` - PDF compilation log.
- `PROVENANCE.md` - revision, CI, and source provenance.
- `INTEGRATION.md` - review and integration procedure.
- `MANIFEST.txt` and `SHA256SUMS` - archive inventory and hashes.

## Reproduction

From a checkout of BusyLean at the stated base commit:

```bash
git apply integration/contender7.patch
python3 scripts/check.py
```

Or overlay the `lean/` directory onto a current checkout and run:

```bash
lake build BusyLean.Contender7
lake build
lake env lean test/Contender7Audit.lean
```

Do not attempt `#eval BusyLean.contender_7`.

## Important interpretive boundary

The strict comparisons and computability claims are kernel-checked.  The article's Veblen-style and fast-growing-hierarchy discussion is explicitly heuristic pending a formal ordinal quotient, rank semantics for `OTree`/`WTree`, normality proofs for the critical-point operators, and a calibrated domination theorem for `stage`.
