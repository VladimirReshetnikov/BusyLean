# Artifact manifest

- `article/contender14.tex` - full research article source.
- `article/contender14.pdf` - compiled 22-page article.
- `repo_overlay/BusyLean/Contender14.lean` - definition module.
- `repo_overlay/BusyLean/Comparison14.lean` - comparison theorem module.
- `repo_overlay/BusyLean.lean.additions` - imports to append to the root module.
- `repo_overlay/test/Audit14.lean` - audit commands to merge into the existing
  audit file.
- `repo_overlay/scripts/check14.py.patch-notes` - timing-script changes.
- `contender14.patch` - unified patch against the recorded baseline.
- `README_INTEGRATION.md` - application and validation instructions.
- `PROPOSAL_SUMMARY.md` - concise construction and theorem summary.
- `BASELINE.md` and `SOURCE_PROVENANCE.md` - exact target and reused components.
- `VALIDATION.md` - completed checks and explicit limitations.
- `validation/validate_overlay.py` - reproducible static preflight.
- `validation/*.txt` and `validation/latex-build.log` - recorded validation
  output.
- `SHA256SUMS` - hashes for all distributed files except the checksum ledger
  itself.
