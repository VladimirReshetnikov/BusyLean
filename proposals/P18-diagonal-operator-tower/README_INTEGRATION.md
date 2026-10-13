# Contender 14 overlay

## Files to add

Copy these files into the repository:

- `repo_overlay/BusyLean/Contender14.lean` -> `BusyLean/Contender14.lean`
- `repo_overlay/BusyLean/Comparison14.lean` -> `BusyLean/Comparison14.lean`

Append the two imports from `repo_overlay/BusyLean.lean.additions` to
`BusyLean.lean`.

Merge the commands in `repo_overlay/test/Audit14.lean` into `test/Audit.lean`.
Update `scripts/check.py` as described in
`repo_overlay/scripts/check14.py.patch-notes`.

A ready-to-apply unified diff is included as `contender14.patch`:

```bash
git checkout 1ee50c7d97bbed57a60709f661453c3e213f4db3
git apply --check contender14.patch
git apply contender14.patch
```

For a later `main`, rebase the small root-import, audit, and check-script hunks;
the two new Lean modules are self-contained additions.

## Required validation

From a clean checkout at the recorded baseline (or after rebasing):

```bash
python3 validation/validate_overlay.py
python3 scripts/check.py
lake env lean test/Audit.lean
```

The first command is only a static preflight. The latter two commands are the
Lean 4.34.0 kernel, timing, axiom, and dependency-closure checks required by the
contest rules.

## Construction in one line

```lean
def contender_14 : Nat := F14 (F14 42)
```

Here `F14 n` runs a dynamic-kind family-reflection transformer through a
rank-dependent diagonal tower of operator stages whose height is
`family13 n = F13 (F13 n)`. At `n = 42`, that height is definitionally
Contender 13, while the executable definition never mentions the previous
closed contender constant.

The comparison module also states:

- strict growth from every lower tower rank to every higher tower rank;
- domination of every bounded dynamic-kind program run with the packed
  predecessor-family oracle; and
- the required `contender_13 < contender_14` theorem.

## Current validation status

The static overlay check, patch-application preflight, LaTeX build, PDF
preflight, and 22-page render inspection passed. Lean kernel compilation was
not available in the artifact environment and remains mandatory; see
`VALIDATION.md`.
