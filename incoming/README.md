# `incoming/`: the drop zone for proposals

This directory is where **new contest proposals arrive**, usually as `.zip`
archives. Nothing here is part of the verified library. Archives are
untrusted input until they have been processed.

## What happens to an archive

Each archive goes through the same pipeline, and the git history records
every step as a separate commit:

1. **Unpack.** The archive is extracted into its own empty scratch
   directory (never into the working tree directly) and inspected. Lean
   sources are screened for code that runs at elaboration time (`#eval`,
   `run_cmd`, `initialize`, IO).
2. **Import.** The unpacked tree is copied *unmodified* into
   [`../proposals/`](../proposals) under a descriptive name (`P1-…`,
   `P2-…`, …). Checksum ledgers are dropped by the repository's
   `.gitignore` policy.
3. **Build.** The proposal is rebuilt with the pinned toolchain (see
   [`../lean-toolchain`](../lean-toolchain)), usually on a scratch git
   worktree at the commit it targets. Its own scripts are not run; the
   reviewer runs `#print axioms` and dependency checks. Minimal repairs, if
   any, are made in separate, documented commits.
4. **Review.** The results go into
   [`../proposals/REVIEW.md`](../proposals/REVIEW.md): build status, axioms,
   timing, what the construction does, an informal size estimate, and how it
   compares with the current contender. Reusable ideas may be adopted into a
   new contender, with attribution in the source.
5. **Delete.** The processed archive is removed from this directory.

So an empty `incoming/` (apart from this file) means every proposal received
so far has been processed.

## Checklist for submitters

A proposal is easiest to evaluate when it:

* targets the **current** contender (see [`../README.md`](../README.md)) and
  states the repository commit it was written against;
* builds with the pinned Lean version and depends only on `propext` and
  `Quot.sound` (no `Classical.choice`, `sorry`, `native_decide`,
  `noncomputable`, `partial`, `unsafe`, `implemented_by`, or `extern`);
* proves `contender_(N-1)_lt_contender_N` without using the constant
  `contender_(N-1)` in the definition (its *construction* may serve as a
  seed or oracle; see rule 5 of the [rules](../README.md#rules-lean-edition));
* fits the time budgets: 15 s for the new definition and 60 s for its proof;
* says plainly whether it was actually compiled, and with which toolchain;
* never asks anyone to evaluate the number.

Most proposals so far amplified an earlier contender's language
(reflection along trees, operator-level reflection, notations above an
index). The largest gains have come from **stronger object languages**:
System F, Fω, kind polymorphism, and universes of operators. See
[`../article/busylean.pdf`](../article/busylean.pdf) for why.
