# Validation record

## Revisions

- Repository: `VladimirReshetnikov/BusyLean`
- Base revision: `64d31a0cf6f1aa4477a088be5554957de6e87a61`
- Branch: `research/contender20-autonomous-wtree-ladder`
- Validated head: `fd43cae755356719c907fde0b0b131d258a30e18`
- Ahead/behind relative to base: `12 / 0`
- Added repository files: `7`
- Added lines: `589`

## CI environment

- Workflow run: `38425930036`
- Job: `115395185372`
- Date: 2026-10-13
- Runner: GitHub-hosted Ubuntu 24.04
- Lean: `4.34.0`, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`
- Lake: `5.0.0-src+293d5d0`

## Contest-style timing

The validator deletes generated build directories, builds the accepted
predecessor, and then times only the new phases.

| Phase | Observed | Budget | Status |
|---|---:|---:|---|
| `lake build BusyLean.Comparison19` | 20.061 s | not charged | pass |
| `lake build BusyLean.Contender20` | 0.746 s | 15 s | pass |
| `lake build BusyLean.Comparison20` | 0.454 s | 60 s | pass |
| Total clean build | 21.261 s | - | pass |

## Smoke test

`test/WTreeLadderSmoke.lean` printed:

```text
true
true
true
true
true
false
TreePath.childLt_wf : forall (root : WTree Nat),
  WellFounded fun b a => TreePath.childLt root b a = true
wLevel_wf : WellFounded BusyLean.FL.ALt
follow_tree12 :
  TreePath.follow autonomousUniverseTree (TreePath.root.child 0) =
    some BusyLean.tree12
```

The five `true` values check valid paths and parent-child edges in a tiny tree;
the final `false` checks that the root is not below itself.

## Axiom audit

```text
'BusyLean.contender_20' depends on axioms: [propext, Quot.sound]
'BusyLean.contender_19_lt_contender_20' depends on axioms: [propext, Quot.sound]
'BusyLean.family19_lt_F20' depends on axioms: [propext, Quot.sound]
'BusyLean.orbit19_lt_F20' depends on axioms: [propext, Quot.sound]
'BusyLean.long_F19_orbit_lt_contender_20' depends on axioms: [propext, Quot.sound]
'BusyLean.avalue_lt_F20' depends on axioms: [propext, Quot.sound]
'BusyLean.orbit19_lt_next' depends on axioms: [propext, Quot.sound]
'BusyLean.Ordinal.wLevel_wf' depends on axioms: [propext]
'BusyLean.FL.sn_erase_wlevel' depends on axioms: [propext, Quot.sound]
```

The script accepted all nine declarations under the permitted set
`{propext, Quot.sound}`.

## Dependency closure

```text
BusyLean.contender_20: closure of 4235 constants avoids all 15 forbidden names
```

The forbidden names are the closed constants `BusyLean.contender_5` through
`BusyLean.contender_19`. The new definition intentionally uses `F19` and other
shared repository machinery; the check prevents simply embedding an earlier
closed contender constant.

## Main theorem types

```text
BusyLean.contender_19_lt_contender_20 :
  BusyLean.contender_19 < BusyLean.contender_20

@BusyLean.orbit19_lt_F20 :
  forall {i n : Nat}, i <= n -> BusyLean.orbit19 i n < BusyLean.F20 n

BusyLean.long_F19_orbit_lt_contender_20 :
  BusyLean.iterateF19 (BusyLean.F20 42 + 2) (BusyLean.F20 42) <
    BusyLean.contender_20

@BusyLean.avalue_lt_F20 :
  forall {n : Nat} {t : BusyLean.FL.CTm BusyLean.Ordinal.WLevel},
    t in BusyLean.FL.autonomousLadderUpTo n ->
      BusyLean.FL.avalue (BusyLean.packFamily BusyLean.orbit19) n t <
        BusyLean.F20 n
```

## Reproduction command

```bash
python3 scripts/check_contender20.py
```
