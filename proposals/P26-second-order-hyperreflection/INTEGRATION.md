# Integration instructions

The overlay is intended for BusyLean `main` at tree
`64d31a0cf6f1aa4477a088be5554957de6e87a61` or a nearby descendant retaining
the Contender 19 API.

## Apply

From the BusyLean repository root, either apply the patch:

```bash
git apply /path/to/busylean_contender20.patch
```

or copy the overlay manually:

```bash
cp -R /path/to/repo_overlay/BusyLean/. BusyLean/
cp /path/to/repo_overlay/test/SecondOrderReflectionSmoke.lean test/
cat >> BusyLean.lean <<'LEAN'
import BusyLean.SecondOrderReflection
import BusyLean.SecondOrderReflectionFacts
import BusyLean.Contender20
import BusyLean.Comparison20
LEAN
```

Insert `README_INSERT.md` above the existing Contender 19 section if the
proposal is accepted.

## Build and check

The repository pins Lean 4.34.0. Run:

```bash
lake build BusyLean.Comparison20
lake env lean test/SecondOrderReflectionSmoke.lean
```

Then perform the full checks:

```bash
lake build
lake env lean test/Audit.lean
```

A convenience wrapper runs the focused checks against an already patched checkout:

```bash
/path/to/package/scripts/build_and_audit.sh /path/to/BusyLean
FULL_BUILD=1 /path/to/package/scripts/build_and_audit.sh /path/to/BusyLean
```

The smoke file deliberately uses only `#check` and `#print axioms`; it never
tries to normalize or evaluate `contender_20`.

## Expected public declarations

```text
BusyLean.HyperLift
BusyLean.spliceLifts
BusyLean.stageHyperLift
BusyLean.liftLift
BusyLean.diagonalHyperLift
BusyLean.GoodLift
BusyLean.diagonalHyperLift_preservesGoodLifts
BusyLean.diagonalHyperLift_strictlyLiftInflationary
BusyLean.diagonalHyperLift_rank_lt_succ
BusyLean.family19
BusyLean.schedule20
BusyLean.rank20
BusyLean.baseLift20
BusyLean.firstOrder20
BusyLean.F20
BusyLean.contender_20
BusyLean.family19_lt_firstOrder20
BusyLean.firstOrder20_lt_F20
BusyLean.family19_lt_F20
BusyLean.contender_19_lt_contender_20
```

## Failure triage

If elaboration attempts to unfold a huge numerical definition, preserve the
current proof shape: prove inequalities through `Progressive`, `GoodLift`, and
explicit child/splice witnesses. Do not use broad `simp` sets containing
`F19`, `family19`, `schedule20`, `rank20`, `F20`, or `contender_20`.

If the `change` in `base_lt_stageHyperLift` becomes sensitive to reducibility,
replace it with two local `rfl` equalities exposing `spliceLifts` and
`stageHyperLift`; do not rewrite with contender definitions.
