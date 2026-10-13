# Contender 20 validation receipt

- Repository: `VladimirReshetnikov/BusyLean`
- Branch: `research/w-ranked-contender20-20261013`
- Validated commit: `af98b262699f4d19712682fc9a0cffe2ed353217`
- GitHub Actions run: `38424692293`
- Job: `115390885823`
- Artifact: `contender20-validation`, artifact ID `11827144194`
- Artifact SHA-256 reported by GitHub:
  `3b85c0bc0d13af2322ba15a1292388da3562f8ce8bc84dc559178647cf96b13a`
- Runner: Ubuntu 24.04
- Lean: 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`
- Lake: 5.0.0

## Timings recorded by the workflow

| Phase | Result | Wall time |
|---|---:|---:|
| Accepted base through `BusyLean.Comparison19` | success | 19.25 s |
| New definitions through `BusyLean.Contender20` | success | 0.84 s |
| New comparison proofs through `BusyLean.Comparison20` | success | 0.35 s |
| Focused audit | success | approximately 1.04 s |

## Axiom audit output

- `BusyLean.spliceLifts`: no axioms.
- `BusyLean.wDiagonalLift` and generic W-rank theorems: `propext`.
- `BusyLean.F20`, `BusyLean.contender_20`, and final comparison:
  `propext`, `Quot.sound`.

## Dependency closure

The audit reported:

```text
BusyLean.contender_20: closure of 4186 constants avoids all 15 forbidden names
```

The forbidden names were the constants `BusyLean.contender_5` through
`BusyLean.contender_19`.

## Checked principal theorem

```lean
BusyLean.contender_19_lt_contender_20 :
  BusyLean.contender_19 < BusyLean.contender_20
```

See `validation-ci.log` for the complete raw receipt.
