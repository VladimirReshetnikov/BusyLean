# Build status

| Check | Status | Evidence |
|---|---|---|
| Lean source static audit | PASS | `STATIC_AUDIT.json` |
| LaTeX compilation | PASS | `article/contender20.pdf`, 25 pages |
| PDF visual inspection | PASS | all pages rendered at 150 dpi and inspected |
| Lean 4.34.0 elaboration | NOT RUN | `lean`/`lake` absent from runtime |
| Kernel comparison theorem | NOT RUN | requires repository toolchain |
| Axiom audit | NOT RUN | commands supplied in `test/Audit20.lean` |
| Clean-build time budgets | NOT RUN | requires reference build environment |

The absence of a Lean receipt is a verification boundary, not evidence of a
failure. The package deliberately distinguishes source-level proof design from
kernel-checked acceptance.
