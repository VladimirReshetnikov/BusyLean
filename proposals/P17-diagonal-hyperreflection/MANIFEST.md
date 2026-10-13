# Package manifest

## Article

- `article/contender14_diagonal_hyperreflection.tex` — complete LaTeX source.
- `article/contender14_diagonal_hyperreflection.pdf` — compiled 19-page paper.

## Lean overlay

- `overlay/BusyLean/HyperReflection.lean` — generic arbitrary-lift stage and diagonal hierarchy.
- `overlay/BusyLean/HyperReflectionFacts.lean` — progressivity, strict inflation, and rank-growth proofs.
- `overlay/BusyLean/Contender14.lean` — dynamic-kind family reflection and the new number.
- `overlay/BusyLean/Comparison14.lean` — comparison and program-domination theorems.
- `overlay/test/Contender14Audit.lean` — axiom, closure, signature, and small-execution audit.
- `overlay/scripts/check_contender14.py` — budget-faithful clean-build checker.
- `overlay/.github/workflows/validate-contender14.yml` — validated CI workflow.

## Integration

- `integration/apply_overlay.sh` — idempotent installer for a BusyLean checkout.
- `integration/BusyLean.lean.patch` — import patch for the root aggregation module.
- `integration/Audit_integration_snippet.lean` — optional additions to the repository-wide audit.
- `integration/README.md` — manual and automated integration instructions.

## Validation records

- `validation/build_timing.txt` — clean and predecessor-cached timings.
- `validation/axiom_audit.txt` — permitted-axiom results.
- `validation/closure_audit.txt` — no-use-of-earlier-contender-constants result.
- `validation/source_guard.txt` — forbidden-construct scan.
- `validation/theorem_signatures.txt` — principal checked theorem types.
- `validation/provenance.txt` — repository baseline, branch, commit, and workflow runs.
- `validation/latex_build.log` — final PDF compilation log.
- `validation/pdf_quality_check.txt` — visual/render inspection record.

`SHA256SUMS` records hashes of every packaged file other than itself.
