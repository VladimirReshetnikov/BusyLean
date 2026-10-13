# BusyLean Contender 20: Autonomous W-Tree Universe Reflection

This archive proposes a new computable-in-principle natural number for
[`VladimirReshetnikov/BusyLean`](https://github.com/VladimirReshetnikov/BusyLean).
It was developed and kernel-checked against:

- base `main` revision: `64d31a0cf6f1aa4477a088be5554957de6e87a61`
- validated research revision: `fd43cae755356719c907fde0b0b131d258a30e18`
- research branch: `research/contender20-autonomous-wtree-ladder`
- Lean: `4.34.0`
- GitHub Actions run: `38425930036`

The isolated branch is 12 commits and 7 added source/test/CI files ahead of the
base. Nothing in this archive has been merged into `main`.

## Proposed number

The core definitions are:

```lean
def orbit19 : Family := fun i n => iterateF19 (i + 2) n

def seedHeight20 (n : Nat) : Nat := orbit19 (family19 n) n

def schedule20 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (seedHeight20 n + 42)
      (Autonomous.encode Ordinal.autonomousUniverseTree))

def rank20 (n : Nat) : Nat := seedHeight20 n + 1

def F20 (n : Nat) : Nat :=
  diagonalLift (schedule20 n) (rank20 n)
    aTransformer orbit19 n n

def contender_20 : Nat := F20 (F20 42)
```

The new object language uses a ramified universe hierarchy indexed by valid
finite addresses in a countably branching well-founded W-tree. Its root joins
`tree12` with every finite autonomous hyper-closure above `tree12`. The
reflection seed exposes an increasing finite orbit of `F19`; coordinate `i` is
the `(i + 2)`-fold iterate of `F19`.

## Exact Lean theorems

The required comparison is kernel checked:

```lean
theorem contender_19_lt_contender_20 :
  contender_19 < contender_20
```

A stronger closed lower bound demonstrates a large gap:

```lean
theorem long_F19_orbit_lt_contender_20 :
  iterateF19 (F20 42 + 2) (F20 42) < contender_20
```

The proposal also proves:

- structural well-foundedness of the W-tree address order;
- strong normalization of typed terms in the W-tree universe language;
- domination of every visible `F19`-orbit coordinate;
- domination of every enumerated W-tree-ladder program at the same input;
- strict inflationarity of `F20` without assuming monotonicity of `F19` or
  reflection.

## Validation result

The final clean GitHub Actions run first built the accepted predecessor and
then timed only the new phases:

| Phase | Time | Budget | Result |
|---|---:|---:|---|
| Prebuild through `BusyLean.Comparison19` | 20.061 s | not charged | pass |
| New definitions through `BusyLean.Contender20` | 0.746 s | 15 s | pass |
| New proofs through `BusyLean.Comparison20` | 0.454 s | 60 s | pass |
| Smoke and axiom/dependency audit | - | - | pass |

Nine declarations were audited. They use only `propext` and `Quot.sound`;
`BusyLean.Ordinal.wLevel_wf` uses only `propext`. A transitive constant-closure
check found 4,235 reachable constants and none of the 15 forbidden named
contender constants (`contender_5` through `contender_19`). The definition does
intentionally reuse the function `F19` and existing generic machinery.

## Reproduce

Copy the repository-relative files from this archive into a checkout at the
base revision and run:

```bash
python3 scripts/check_contender20.py
```

The script performs a clean predecessor build, enforces the incremental timing
budgets, runs the W-tree smoke test, prints the main theorem types and axioms,
and checks the transitive dependency closure.

To compile the article from the archive root:

```bash
cd article
latexmk -pdf contender20.tex
```

## Archive map

- `article/contender20.pdf` - 20-page research article.
- `article/contender20.tex` - complete LaTeX source.
- `article/references.bib` - reusable BibTeX records.
- `BusyLean/Ordinal/WTreeLadder.lean` - tree addresses, validity, order, and
  well-foundedness.
- `BusyLean/Contender20.lean` - language evaluator and number definition.
- `BusyLean/Comparison20.lean` - exact comparison and lower-bound proofs.
- `test/WTreeLadderSmoke.lean` - small executable sanity checks.
- `test/Contender20Audit.lean` - axiom and transitive-closure audit.
- `scripts/check_contender20.py` - clean contest-style validator.
- `.github/workflows/contender20-check.yml` - isolated CI workflow.
- `integration/contender20.patch` - patch containing the seven validated
  repository additions.
- `integration/INTEGRATION.md` - review and integration instructions.
- `validation/VALIDATION.md` and `validation/ci-log.txt` - recorded result.
- `RESEARCH_NOTES.md` - design alternatives, exact/heuristic boundary, and
  further work.
- `MANIFEST.txt` and `SHA256SUMS` - archive inventory and checksums.

## Scientific scope

The formal numerical inequalities and normalization statements are exact Lean
theorems. The article deliberately does **not** assign a standard named
proof-theoretic ordinal to the autonomous W-tree language, nor claim a formal
language-strength embedding of the existing large-Veblen ladder. Those are
identified as future research questions rather than treated as established
facts.
