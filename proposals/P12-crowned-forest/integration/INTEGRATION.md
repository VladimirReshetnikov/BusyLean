# Integration into BusyLean

The proposal is pinned to BusyLean commit
`4c4b03d0e2003c479e3bee90a21c8bea13f66c40` (the Contender 10 documentation
commit).  Review repository drift before applying it to any later revision.

## Safe route

From this package:

```bash
python3 integration/install.py /path/to/BusyLean
```

This is a dry run and prints unified diffs.  After review:

```bash
python3 integration/install.py /path/to/BusyLean --apply
python3 scripts/check_in_repo.py /path/to/BusyLean
```

`check_in_repo.py` expects the two modules to be installed; alternatively pass
`--install`.  It performs the same three-phase timing discipline as the
repository checker:

1. build `BusyLean.Comparison10` as the unbudgeted accepted predecessor;
2. build `BusyLean.Contender11` under the 15-second definition budget;
3. build `BusyLean.Comparison11` under the 60-second proof budget;
4. run the definitional smoke tests and the axiom/dependency audit.

The checker never evaluates `contender_10`, `F11 42`, or `contender_11`.

## Files to add

- `BusyLean/Contender11.lean`
- `BusyLean/Comparison11.lean`
- optionally `test/Audit11.lean`
- optionally `test/Contender11Smoke.lean`

## Existing files to update

- Append the two imports in `candidate/BusyLean.lean.append` to `BusyLean.lean`.
- Merge `candidate/test/Audit.lean.append` into `test/Audit.lean`.
- In `scripts/check.py`, set:

```python
PREVIOUS = "BusyLean.Comparison10"
CURRENT_DEF = "BusyLean.Contender11"
```

The supplied installer makes exactly these edits and refuses to overwrite
conflicting candidate files.

## Expected review points

1. **Definitional reduction at `root_program_lt_F11`.**  The proof asks Lean to
   unfold one crown node and one `stage11` node.  If elaboration does not accept
   the `change`, replace it with two explicit `rw`/`simp only` steps; do not
   introduce numerical evaluation.
2. **Crown induction normal forms.**  If `k + 1` and `Nat.succ k` do not align
   definitionally in a particular elaboration context, add `simpa [Nat.succ_eq_add_one]`.
3. **Timing.**  The definition module is small, but it imports Contender 10.
   The repository rules allow the predecessor to be precompiled; use the
   three-phase checker rather than timing a full historical rebuild against
   the 15-second budget.
4. **Axioms.**  The new proof layer should add no axioms beyond those inherited
   from the accepted normalization development.  The supplied audit checks the
   actual transitive closure.
