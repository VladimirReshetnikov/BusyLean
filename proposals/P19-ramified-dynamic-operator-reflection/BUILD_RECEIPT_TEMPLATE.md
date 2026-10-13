# BusyLean Contender 14 build receipt

## Environment

- Date/time (UTC):
- Operator:
- Repository URL:
- Baseline commit:
- Commit after overlay:
- Operating system:
- CPU:
- RAM:
- Filesystem / virtualization notes:
- `lean --version`:
- `lake --version`:
- SHA-256 `BusyLean/Contender14.lean`:
- SHA-256 `BusyLean/Comparison14.lean`:

## Clean build

Command:

```bash
python3 scripts/check.py
```

Exit status:

```text

```

Unedited stdout/stderr:

```text

```

Reported times:

- previous contender:
- definitions (budget 15 s):
- proofs (budget 60 s):
- total clean build:

## Standalone audit

Command:

```bash
lake env lean test/Contender14Audit.lean
```

Exit status:

```text

```

Unedited stdout/stderr:

```text

```

## Required conclusions

- [ ] `BusyLean.contender_14` kernel-checks.
- [ ] `BusyLean.contender_13_lt_contender_14` kernel-checks.
- [ ] `BusyLean.fortyTwo_F13_steps_lt_F14` kernel-checks.
- [ ] `BusyLean.fvalue_lt_contender_14` kernel-checks.
- [ ] Only permitted axioms appear.
- [ ] Dependency closure excludes all predecessor contender constants.
- [ ] Definition time is at most 15 seconds.
- [ ] Proof time is at most 60 seconds.
- [ ] No contender was evaluated.

## Notes / repairs

Record every source change made after unpacking the archive, including a diff
and an explanation of why it preserves the proposed definitions and claims.
