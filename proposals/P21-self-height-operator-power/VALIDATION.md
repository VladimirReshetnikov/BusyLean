# Validation status

## Completed in this package build

- Inspected BusyLean `main` at commit
  `0cd13c0c2607b4fcb461090a95f356e538c0fc5b` and recorded the repository
  snapshot in `source_snapshot.json`.
- Matched the public signatures of `Fd.reflectFd`, `Fd.fvalue`, `Progressive`,
  `operatorStage`, `operatorStage_progressive`,
  `transformer_lt_lift_at`, and `operatorStage_child_lt`.
- Ran `scripts/static_audit.py` successfully. It found no forbidden construct,
  no prior `contender_N` constant in the comment-stripped definition, no
  missing required declaration, and no Lean source line over 100 columns.
- Byte-compiled both Python audit scripts.
- Generated `integration/contender14_new_files.patch` and verified it with
  `git apply --check` in a clean temporary Git repository.
- Compiled the LaTeX article with `latexmk` to a 16-page PDF with resolved
  references and no overfull-box warning.
- Preflighted the PDF, confirmed embedded fonts, rendered every page to PNG,
  inspected the full montage and selected pages at larger scale, and
  spot-checked extracted text.
- Generated a SHA-256 manifest for all delivered artifacts.

## Lean kernel build status

The execution container did not contain the repository-pinned Lean 4.34.0
installation, and its available network path could not retrieve the toolchain
archive. Therefore the Lean files were **not kernel-compiled in this
container**. `scripts/check14.py` and `test/Audit14.lean` are included so the
exact build, timing, axiom, and dependency-closure checks can be run in the
BusyLean checkout with the pinned toolchain.

This limitation is deliberately stated rather than replaced by a claim of
verification. The source is a minimal overlay over the inspected repository
snapshot and follows the already checked proof interfaces of Contenders
11--13 and `MetaReflectionFacts.lean`.
