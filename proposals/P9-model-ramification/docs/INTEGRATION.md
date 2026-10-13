# Integration into BusyLean

1. Check the standalone package against Lean 4.34.0 first. New code is currently
   uncompiled; resolve any elaboration errors and retain the complete logs.
2. In a checkout of commit `86b360648163f0249eab79539438b6a83dfe8215`, copy
   `lean/BusyLean7/` to `BusyLean7/` and `lean/BusyLean7.lean` to `BusyLean7.lean`.
   Do not overwrite the three original baseline files with the vendored copies.
3. Add a `[[lean_lib]]` entry named `BusyLean7` to the existing Lake TOML file.
   Retain the original BigNumber dependency arrangement.
4. Run `lake build BusyLean7`, then the smoke and audit files. They must compile;
   inspect the actual axiom lists and confirm only `propext` / `Quot.sound`.
5. `integration/Transitive.lean` can then use the full repository's existing
   C5 and P5 comparison theorems. P1-P4 need separate explicit translations or
   comparison proofs; their informal ranking is not a substitute.
6. Record clean-build times under the repository's own 15/60-second rules.
   Update the evidence ledger only from actual new runs.

The submission constant is `BusyLean.contender_7`. The direct theorem is
`BusyLean.contender_6_lt_contender_7`, and the stronger one is
`BusyLean.contender_6_tower_lt_contender_7`. No remote repository was modified
while preparing this package.
