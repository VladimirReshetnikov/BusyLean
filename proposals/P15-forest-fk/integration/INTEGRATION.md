# Integration into BusyLean

This package targets BusyLean commit
`4c4b03d0e2003c479e3bee90a21c8bea13f66c40`.


## Apply the supplied patch

From a clean checkout of the pinned commit, the complete source/audit/script
change can be applied with:

```bash
git apply patches/0001-contender11.patch
```

The patch was generated and test-applied against the exact `BusyLean.lean`
content at the target snapshot.  The article and verification receipt remain
separate review artifacts and are not injected into the repository by that
patch.

## Files to copy

Copy these files into the repository at the same relative paths:

- `BusyLean/Contender11.lean`
- `BusyLean/Comparison11.lean`
- `test/Contender11Audit.lean`
- `scripts/check_contender11.py`

## Umbrella module

Append to `BusyLean.lean`:

```lean
import BusyLean.Contender11
import BusyLean.Comparison11
```

## Main audit

The supplied standalone audit is sufficient for review.  For the repository's
main `test/Audit.lean`, add the five `#print axioms` lines and the closure check
shown in `test/Contender11Audit.lean`.

## Contest timing script

The supplied `scripts/check_contender11.py` stages the build as follows:

1. `BusyLean.Comparison10` as accepted history;
2. `BusyLean.Contender11` under the 15 second definition budget;
3. `BusyLean.Comparison11` under the 60 second proof budget;
4. `test/Contender11Audit.lean`.

Run:

```bash
python3 scripts/check_contender11.py
```

Do not evaluate `BusyLean.contender_11`.

## Reproduce the independent remote check

From this package directory, with Internet access:

```bash
python3 scripts/verify_axle.py
```

The script pins both the BusyLean snapshot and Lean 4.34.0.  The recorded run is
in `verification/AXLE_REPORT.md` and `verification/AXLE_REPORT.json`.

## Suggested README entry

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)
def F11 (n : Nat) : Nat := stage11 (fun _ => family10) index n
def contender_11 : Nat := F11 (F11 42)

theorem contender_10_lt_contender_11 : contender_10 < contender_11
```

Describe Contender 11 as forest reflection of kind-polymorphic System F-omega
along the W-language's self-index.  The formal margin is stronger than a single
strict inequality: `family10_lt_F11` holds at every input,
`fvalue_lt_contender_11` covers every enumerated kind-polymorphic program at the
final inner budget, and `defined_tree_eventually_lt11` covers every W-language
definable index tree.
