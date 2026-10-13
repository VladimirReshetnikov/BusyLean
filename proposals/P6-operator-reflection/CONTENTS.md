# Bundle contents

## Primary deliverables

- `article/contender7.tex` - 21-page research article source.
- `article/contender7.pdf` - compiled and render-checked article.
- `patches/contender7.patch` - unified patch against BusyLean commit
  `86b360648163f0249eab79539438b6a83dfe8215`.

## Lean overlay

- `repo_overlay/BusyLean/MetaReflection.lean` - transformer definitions.
- `repo_overlay/BusyLean/MetaReflectionFacts.lean` - progressivity and direct
  comparison lemmas.
- `repo_overlay/BusyLean/Contender7.lean` - the closed number definition.
- `repo_overlay/BusyLean/Comparison7.lean` - comparison and closure theorems.
- `repo_overlay/test/MetaReflectionSmoke.lean` - executable tiny examples.
- `repo_overlay/test/Contender7Audit.lean` - axiom and dependency-closure audit.
- `repo_overlay/scripts/check_contender7.py` - clean build, timing, smoke, and
  audit driver.
- `repo_overlay/BusyLean.lean` - aggregate imports.
- `repo_overlay/CONTENDER7.md` - repository-facing proposal note.

## Independent validation and research aids

- `scripts/static_audit.py` - source-level contest-rule checks.
- `scripts/check_contender7.py` - copy of the integration driver.
- `scripts/ordinal_skeleton.py` - finite exponent bookkeeping regression model.
- `validation/VALIDATION.md` - completed and outstanding checks.
- `validation/MANUAL_LEAN_REVIEW.md` - manual proof-engineering review.
- `validation/contact_sheet.png` - final PDF page contact sheet.
- `validation/pdf_inspect.txt`, `pdf_preflight.txt`, and
  `pdf_text_checks.txt` - PDF verification records.
- `validation/patch_apply_output.txt` - clean patch application record.
- `SHA256SUMS` - checksums for all files in the bundle except itself.
