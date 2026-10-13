# Verification report

## Result

**PASS.** The proposal was kernel-checked with the BusyLean repository's exact
pinned Lean toolchain, `leanprover/lean4:v4.34.0`.

- Baseline repository commit: `43513401d8929d60b2e3e40a4a20835a1271e94f`
- Isolated verification branch: `research/contender35-metalanguage-20261013`
- Verified branch commit: `f08df5f2a4cb21ec847d1fe3b9a95f7818a9e78e`
- GitHub Actions workflow run: `38440600428`
- Workflow conclusion: `success`
- Artifact ID: `11834996628`
- Artifact SHA-256 reported by GitHub:
  `c02ee252cba93bc89adbd3daba3ea846cd7aad11e3a8b0a586fb37c58d900331`

The branch is verification-only; the repository's `main` branch was not
modified.

## Kernel-checked modules

```text
BusyLean.Ordinal.TreeLanguage4
BusyLean.Contender35
BusyLean.Comparison35
```

All three built successfully.  In particular, Lean accepted:

```lean
BusyLean.contender_35 : Nat
BusyLean.contender_34_lt_contender_35 :
  BusyLean.contender_34 < BusyLean.contender_35
```

## Timings

The accepted repository baseline was precompiled first, matching BusyLean's
contest timing convention.  The new modules then measured:

| Module | Wall time | Peak RSS |
|---|---:|---:|
| `BusyLean.Ordinal.TreeLanguage4` | 0.53 s | 539,256 KiB |
| `BusyLean.Contender35` | 0.33 s | 542,344 KiB |
| `BusyLean.Comparison35` | 0.33 s | 541,764 KiB |

These are GitHub-hosted Ubuntu runner measurements, not claims about all
machines.

## Axiom audit

Exact output:

```text
'BusyLean.Ordinal.MTL.Tm.eval' does not depend on any axioms
'BusyLean.Ordinal.metaLangLift' depends on axioms: [propext]
'BusyLean.Ordinal.metaBoostT' depends on axioms: [propext]
'BusyLean.Ordinal.metaLanguageTree' depends on axioms: [propext]
'BusyLean.contender_35' depends on axioms: [propext, Quot.sound]
'BusyLean.contender_34_lt_contender_35' depends on axioms: [propext, Quot.sound]
'BusyLean.metavalue_lt_F35' depends on axioms: [propext, Quot.sound]
```

This is within BusyLean's stated allowance of `propext` and `Quot.sound`.
The new semantic interpreter itself is axiom-free.

## Dependency-closure audit

Exact output:

```text
BusyLean.contender_35: closure of 5534 constants avoids all 30 forbidden names
```

The forbidden list contains every prior contender constant from
`BusyLean.contender_5` through `BusyLean.contender_34`.  The new definition uses
Contender 34's *construction* through `F34`, `schedule34`, and related reusable
infrastructure, but it does not smuggle the previous final constant into the
new term.

## Reproduction

From a checkout containing the proposed files:

```bash
lake build BusyLean.Ordinal.TreeLanguage4
lake build BusyLean.Contender35
lake build BusyLean.Comparison35
lake env lean test/Contender35Audit.lean
```

The raw logs are included under `verification/`.
