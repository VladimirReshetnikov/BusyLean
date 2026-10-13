# BusyLean Contender 20: second-order diagonal hyperreflection

This research package proposes a new closed, structurally computable Lean
number for the BusyLean repository:

```lean
def contender_20 : Nat := F20 (F20 42)
```

The construction makes a type-level jump beyond the current Contender 19.
Contender 19 diagonalizes **transformer lifts**. Contender 20 introduces
**hyperlifts**, which transform entire transformer-lift hierarchies, and then
performs a predecessor-sized diagonal hierarchy at that new level.

The formal comparison is intentionally factored through an explicit witness:

```lean
theorem family19_lt_firstOrder20 (n : Nat) :
  family19 n < firstOrder20 n

theorem firstOrder20_lt_F20 (n : Nat) :
  firstOrder20 n < F20 n

theorem contender_19_lt_contender_20 :
  contender_19 < contender_20
```

Thus `F20 n` contains a complete first-order diagonal layer of rank
`family19 n + 1` and then strictly exceeds that layer by second-order diagonal
hyperreflection.

## Package contents

- `article/contender20_second_order_hyperreflection.tex` — research article.
- `article/contender20_second_order_hyperreflection.pdf` — compiled article.
- `repo_overlay/BusyLean/SecondOrderReflection.lean` — new second-order
  definitions.
- `repo_overlay/BusyLean/SecondOrderReflectionFacts.lean` — generic strict
  growth theorems.
- `repo_overlay/BusyLean/Contender20.lean` — the proposed number.
- `repo_overlay/BusyLean/Comparison20.lean` — the formal comparison chain.
- `repo_overlay/test/SecondOrderReflectionSmoke.lean` — non-evaluating smoke
  and axiom checks.
- `busylean_contender20.patch` — patch adding the modules and imports.
- `README_INSERT.md` — proposed repository README section.
- `INTEGRATION.md` — exact integration and build commands.
- `VALIDATION.md` and `BUILD_STATUS.md` — validation scope, evidence, and limitations.
- `figures/theorem_graph.*` — proof dependency graph.
- `scripts/static_audit.py` — source-hygiene audit.
- `validation/` — static-audit, patch-integrity, LaTeX, PDF-preflight, and metrics records.
- `MANIFEST.md` and `MANIFEST.sha256` — inventory and reproducibility hashes.
- `LICENSE` — repository-compatible MIT No Attribution license.

## Baseline

The package was designed against BusyLean `main` tree
`64d31a0cf6f1aa4477a088be5554957de6e87a61`, whose README names Contender 19
as the incumbent. The repository pins Lean `v4.34.0`.

## Important validation note

The LaTeX article, 20-page PDF render inspection, patch-integrity check, and
static source audit were executed in this environment. A Lean 4.34.0 executable
was not available here, so the supplied Lean overlay has **not** been
kernel-checked in this package-generation environment. The
proofs were written to mirror the already accepted `HyperReflectionFacts`
architecture and avoid reduction of any contender-sized term. Run the commands
in `INTEGRATION.md` before merging.
