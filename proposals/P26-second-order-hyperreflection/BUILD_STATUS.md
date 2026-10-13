# Build and validation status

| Check | Status | Evidence |
|---|---:|---|
| LaTeX compilation | PASS | `article/contender20_second_order_hyperreflection.pdf`, `validation/latexmk_transcript.txt` |
| PDF preflight | PASS | 20 letter-size pages; all fonts embedded; `validation/pdf_inspect.txt` |
| Visual PDF inspection | PASS | all 20 rendered pages inspected; contact sheet in `validation/pdf_contact_sheet.png` |
| Static Lean source hygiene | PASS | `validation/static_audit.json` |
| Patch integrity | PASS | `validation/patch_check.txt` |
| Lean 4.34.0 kernel build | NOT RUN | toolchain unavailable in the generation environment; exact commands are in `INTEGRATION.md` |

The last row is the acceptance-critical remaining check. Nothing in this package
represents the Lean overlay as kernel-verified until those commands succeed.
