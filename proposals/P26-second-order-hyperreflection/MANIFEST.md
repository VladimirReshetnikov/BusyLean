# Package manifest

## Research result

The package proposes **Contender 20**, a closed natural number built by
second-order diagonal hyperreflection. Its formal comparison architecture is

```text
family19 n < firstOrder20 n < F20 n
contender_19 < contender_20
```

The first strict step embeds a full predecessor-sized first-order
`diagonalLift`; the second strict step applies a hierarchy of hyperlifts, i.e.
endomorphisms of transformer lifts.

## Primary deliverables

| Path | Description |
|---|---|
| `article/contender20_second_order_hyperreflection.tex` | Complete research article source |
| `article/contender20_second_order_hyperreflection.pdf` | Compiled 20-page article |
| `repo_overlay/BusyLean/SecondOrderReflection.lean` | Second-order definitions |
| `repo_overlay/BusyLean/SecondOrderReflectionFacts.lean` | Generic preservation and strict-growth proofs |
| `repo_overlay/BusyLean/Contender20.lean` | Schedule, ranks, `F20`, and closed contender |
| `repo_overlay/BusyLean/Comparison20.lean` | Pointwise and closed comparison chain |
| `repo_overlay/test/SecondOrderReflectionSmoke.lean` | Non-evaluating API and axiom smoke checks |
| `busylean_contender20.patch` | Ready-to-apply repository patch |

## Supporting material

`README_INSERT.md` supplies a proposed repository README section;
`INTEGRATION.md` gives exact build commands; `figures/` contains the theorem
DAG in DOT, PDF, and PNG forms; `scripts/` contains the build wrapper and static
source audit; and `validation/` records every check performed during package
generation.

## Acceptance boundary

The article and PDF are compiled and inspected, the patch applies cleanly to
the audited baseline, and the static constructivity audit passes. The Lean
source still requires an executed Lean 4.34.0 kernel build before it should be
merged or described as formally verified. See `BUILD_STATUS.md` and
`VALIDATION.md`.
