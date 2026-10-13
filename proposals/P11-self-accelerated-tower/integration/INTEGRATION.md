# Integration checklist

1. Copy the two source modules into `BusyLean/`.
2. Copy `Contender11Audit.lean` into `test/`.
3. Copy `check11.py` into `scripts/`.
4. Append the two imports from `BusyLean.lean.additions` to `BusyLean.lean`.
5. Insert `README_INSERT.md` above the existing Contender 10 section.
6. Run `python3 scripts/check11.py` from a clean checkout.
7. Inspect all `#print axioms` reports. Only `propext` and `Quot.sound` are
   permitted by the current repository rules.
8. Confirm the transitive dependency audit reports that `contender_11` avoids
   all earlier contender constants.
9. Record definition/proof/full-build timings in the article before merging.
10. Only after these steps, change the article and README status from
    "proposed" to "kernel-checked".
