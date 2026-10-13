# Provenance and verification record

## Repository state

- Repository: `VladimirReshetnikov/BusyLean`
- Baseline main commit: `86b360648163f0249eab79539438b6a83dfe8215`
- Development branch: `research/autonomous-reflection-c7-20261012`
- Verified branch commit: `c01efa921d20fcb1d731329ef5582fd16c933fcb`

The files in `lean/` are copies of the verified branch contents at the commit above.  The patch in `integration/contender7.patch` is generated against the baseline main commit.

## GitHub Actions verification

- Workflow: `Contender 7 verification`
- Run ID: `38338582554`
- Job ID: `115104200036`
- Workflow artifact ID: `11786325874`
- Artifact SHA-256 reported by GitHub Actions: `9079b7da0ac413455009ce7f4f092a517c387375a83133fea6c99efdf9e21eb0`
- Conclusion: success

The captured output is reproduced verbatim in `verification/contender7-check.log`.

## Toolchain

```text
c01efa921d20fcb1d731329ef5582fd16c933fcb
Lean (version 4.34.0, x86_64-unknown-linux-gnu, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)
Lake version 5.0.0-src+293d5d0 (Lean version 4.34.0)
```

## Verification scope

The checker removes both Lake build directories, then separately times:

1. `lake build BusyLean.Contender7` for the definition phase;
2. `lake build` for the remaining proof phase.

It then runs the historical audit and `test/Contender7Audit.lean`, parses every `#print axioms` report, rejects any axiom outside `{propext, Quot.sound}`, verifies the dependency exclusions, and performs only the feasible input-zero sanity check.

## PDF verification

The article was compiled from the included TeX source and rendered page by page.  All fourteen rendered pages were visually inspected for clipping, overlap, missing glyphs, black boxes, table overflow, and broken URLs.  No such defects were observed.
