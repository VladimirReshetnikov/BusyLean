# Integration guide

## Recommended review order

1. Read `article/contender7_autonomous_reflection.pdf` for the mathematical design, formal guarantees, heuristic calibration, and limitations.
2. Review `lean/BusyLean/Contender7.lean`.  This file contains definitions only and is the portion governed by the definition-time budget.
3. Review `lean/BusyLean/Comparison7.lean`.  In particular, inspect the explicit child-inclusion proofs rather than assuming any monotonicity of reflection.
4. Review `lean/test/Contender7Audit.lean` and `lean/scripts/check.py`.
5. Compare the captured output in `verification/contender7-check.log` with a local clean run.

## Apply as a patch

The patch targets BusyLean main commit:

```text
86b360648163f0249eab79539438b6a83dfe8215
```

Commands:

```bash
git checkout 86b360648163f0249eab79539438b6a83dfe8215
git apply --check /path/to/integration/contender7.patch
git apply /path/to/integration/contender7.patch
python3 scripts/check.py
```

## Overlay method

The `lean/` directory mirrors repository paths.  From the archive root, with `BUSYLEAN` pointing to a checkout:

```bash
rsync -a lean/ "$BUSYLEAN"/
cd "$BUSYLEAN"
python3 scripts/check.py
```

The overlay modifies `BusyLean.lean` and `scripts/check.py`; review those diffs before copying into a checkout with concurrent changes.

## Expected checks

A successful clean run should establish:

- the definitions phase is within 15 seconds;
- the proof phase is within 60 seconds;
- both audit files execute cleanly;
- only `propext` or `Quot.sound` appear in all audited axiom reports;
- the definition's dependency closure avoids the named prior contender values, winner selectors, and comparison theorem;
- `contender7Family 0 = 4`.

Absolute timings are machine-dependent.  The included CI run used an Ubuntu 24.04 GitHub-hosted runner and completed in 1.45 seconds for definitions and 2.15 seconds for the remaining proofs.

## Merge policy recommendation

Treat the kernel-checked comparison and the heuristic ordinal analysis as separate review tracks.  Adoption as a new contender needs only the former, the computability audit, and the contest-rule review.  Exact proof-theoretic labels should remain explicitly provisional until the open semantic obligations listed in the article are mechanized.
