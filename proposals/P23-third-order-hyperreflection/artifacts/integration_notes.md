# Integration notes for BusyLean maintainers

## New imports

Append these imports after the Contender 19 pair in `BusyLean.lean`:

```lean
import BusyLean.SuperReflection
import BusyLean.SuperReflectionFacts
import BusyLean.Contender20
import BusyLean.Comparison20
```

The supplied `install.sh` performs this edit idempotently.

## Validation before adoption

Run the focused harness first:

```bash
python3 scripts/check20.py
```

Only after it passes should the global audit and main `scripts/check.py` be
advanced from Contender 19 to Contender 20.  The equivalent global settings are:

```python
PREVIOUS = "BusyLean.Comparison19"
CURRENT_DEF = "BusyLean.Contender20"
CURRENT_PROOF = "BusyLean.Comparison20"
```

Add the new key declarations to `test/Audit.lean`, print their axioms, add
`BusyLean.contender_20` to the global no-laziness check, and extend the closure
ban for `contender_20` through `contender_5`.

## README/article update after kernel acceptance

A concise accepted-entry summary should distinguish three layers:

1. large-Veblen universe-ladder reflection (`lTransformer`);
2. the accepted natural hierarchy of transformer lifts (`diagonalLift`); and
3. the new W-tree reflection over whole transformer lifts (`liftStage` and
   `superIterate`), followed by final family reflection.

Record actual clean-build timings and the actual constant-closure size from the
acceptance run.  Do not copy the package's pending-status language after replay
has either succeeded or exposed a repair.

## Minimal repair policy

If Lean requests a definitional-equality hint, prefer a local `simpa` or
`change` over altering the construction.  If a theorem statement itself must
change, rerun the static audit, regenerate the article appendices and patch,
and record the difference explicitly.
