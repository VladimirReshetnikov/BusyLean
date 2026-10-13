# Build and validation status

| Check | Status | Evidence |
|---|---|---|
| Baseline repository audited | PASS | `source_audit/baseline.json` |
| Lean source complete, no placeholders | PASS (source-level) | `artifacts/static_audit.json` |
| Earlier contender constants absent from definition modules | PASS (source-level) | `artifacts/static_audit.json` |
| Installer and unified patch | PASS | `artifacts/integration_validation.txt` |
| Article LaTeX compilation | PASS | `article/contender14.pdf` |
| PDF render and visual inspection | PASS | `artifacts/pdf_validation.txt` |
| Lean 4.34.0 kernel replay | NOT RUN HERE | Run `python3 scripts/check14.py` after installation |
| Axiom audit | SCRIPTED, NOT RUN HERE | `overlay/test/Audit14.lean` |
| Definition/proof timing budgets | SCRIPTED, NOT MEASURED HERE | `overlay/scripts/check14.py` |

The environment used to create this archive had `pdflatex`/`latexmk` but did not
have `lean`, `lake`, or `elan`. No statement in the article or package should be
read as claiming kernel acceptance before the supplied replay command succeeds.
