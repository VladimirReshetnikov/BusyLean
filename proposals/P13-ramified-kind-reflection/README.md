# BusyLean Contender 11 proposal: Diagonal Ramified Kind-Reflection

This archive proposes a closed, computable Lean natural number intended to
succeed BusyLean's current Contender 10 at repository snapshot
`4c4b03d0e2003c479e3bee90a21c8bea13f66c40`.

The proposed core is:

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)

def F11 (n : Nat) : Nat :=
  RK.ramified (family10 n + 1) (fun _ => family10) n

def contender_11 : Nat := F11 (F11 42)
```

`RK.reflect` is a family-aware reflector over the repository's
kind-polymorphic System Fω. `RK.autonomous` lifts an arbitrary family operator
through the existing self-indexing W-tree `index`. `RK.ramified (r + 1)` then
lifts the complete rank-`r` operator, rather than merely making another call to
the base reflector. At input 42, the selected rank is definitionally
`contender_10 + 1`, although no earlier contender constant occurs in the
executable definition.

## Main claimed formal margins

The supplied comparison module is designed to establish:

- `family10 n < F11 n` for every input;
- `RK.ramified r seed n < RK.ramified (r + 1) seed n` at every rank;
- every fixed rank is eventually below the input-dependent diagonal;
- every accepted kind-polymorphic program in the current budget is below
  `F11`;
- `contender_10 < contender_11`.

These statements are proved in the supplied Lean source and in the paper-level
argument. They remain **proposed Lean theorems until the modules are compiled
by Lean 4.34.0**. The preparation environment did not contain that toolchain.
No claim of kernel verification is made in this archive.

## Important files

- `article/ramified_kind_reflection.pdf` — 23-page research article.
- `article/ramified_kind_reflection.tex` — complete LaTeX source.
- `lean/BusyLean/Contender11.lean` — computational definitions only.
- `lean/BusyLean/Comparison11.lean` — comparison and hierarchy theorems.
- `lean/test/Contender11Audit.lean` — standalone axiom/dependency audit.
- `patches/0001-contender11-drkr.patch` — patch against the recorded snapshot.
- `scripts/install_into_repo.py` — idempotent checkout installer.
- `scripts/check_contender11.py` — clean-build, timing, and audit harness.
- `python/reference_model.py` — finite hash-consed executable surrogate.
- `validation/` — static checks, PDF inspection, tests, provenance, and hashes.

## Integration route A: installer

From this archive's root:

```bash
python3 scripts/install_into_repo.py --repo /path/to/BusyLean
cd /path/to/BusyLean
python3 scripts/check_contender11.py
```

The installer copies the two modules and audit, adds umbrella imports, updates
the current/previous build targets, and extends the central audit. It is
idempotent; a second run does not duplicate edits.

## Integration route B: patch

From a checkout at the recorded snapshot:

```bash
git apply --check /path/to/0001-contender11-drkr.patch
git apply /path/to/0001-contender11-drkr.patch
python3 scripts/check.py
```

The patch modifies `scripts/check.py` so that it runs both the existing audit
and the standalone Contender 11 audit.

## Local non-kernel validation reproduced in this archive

```bash
python3 scripts/static_audit.py
python3 -m unittest -v python/test_reference.py
bash scripts/build_article.sh
```

The static audit checks forbidden source forms, direct references to old
contender constants, required declaration names, delimiter balance, line
lengths, and source hashes. The Python model checks the defining recurrence and
strictness invariants on a finite surrogate. Neither substitutes for Lean's
kernel.

## Research status

The exact domination proofs do not depend on a speculative ordinal assignment.
The article's proof-theoretic calibration is deliberately labeled heuristic:
if one autonomous lift behaves like multiplication by the self-index's order
type, finite rank resembles repeated multiplication, while the numerical
rank diagonal outruns every fixed finite level. No named-ordinal identity is
claimed as a theorem.

See `validation/lean_build_status.md` and `validation/claim_status.md` for the
precise boundary between completed checks and outstanding acceptance work.
