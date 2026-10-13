# Integrating into the full BusyLean repository

1. Confirm that the baseline matches commit
   `86b360648163f0249eab79539438b6a83dfe8215`, or re-check every affected bridge.
2. Copy `lean/Mirror/*.lean` to a new root `Mirror/` folder and
   `lean/BusyLean/Contender7.lean` to `BusyLean/Contender7.lean`.
3. Add a `Mirror` Lean library to the existing Lake configuration (or move the
   namespace/module layout into the existing library and adjust imports).
   Copy `lean/Mirror.lean` as the library root. Do not replace the repository's
   existing `BusyLean.lean`, lakefile, toolchain, or upstream dependency files.
4. Check definitions, all proofs, `Mirror/Audit.lean`, and `Mirror/Smoke.lean`
   with Lean 4.34.0. The new source is currently uncompiled and may need repairs.
5. Copy/check `PreviousContenders.lean` to inherit C5/P5 comparisons. It imports
   the full repository's comparison module, deliberately not vendored here.
6. Run the repository's clean-budget harness as well as the supplied checker.
   Require both the actual axiom/dependency audit and the timing rules before
   admitting the entry.

The new definition shares p5Family and generic language/reflection operations;
it does not use the named previous winner as a seed. The intended stronger
transitive dependency assertion is in Mirror/Audit.lean. This package has not
modified or pushed to the remote repository.
