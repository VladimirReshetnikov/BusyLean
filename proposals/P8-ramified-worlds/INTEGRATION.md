# Integration into BusyLean

The package does not modify the remote repository. It is pinned to commit
`86b360648163f0249eab79539438b6a83dfe8215` and uses a separate namespace,
`BusyLean.V7`.

The safest first step is to validate the standalone project in `lean/` with
`python3 scripts/check_lean.py`. Compilation has not been performed here.

After a successful build/audit, the modules can be integrated by copying
`lean/BusyLeanNext.lean` and the `lean/BusyLeanNext/` directory to the BusyLean
repository root and adding this library entry to its `lakefile.toml`:

```toml
[[lean_lib]]
name = "BusyLeanNext"
```

Build the new library explicitly with `lake build BusyLeanNext`. There is no
need to replace `BusyLean/Contender6.lean` or import the new number into old
definition modules. Keep proof imports out of the definition module.

The audit and smoke files can live in `test/V7Audit.lean` and
`test/V7Smoke.lean`; their import `BusyLeanNext` remains correct. Copy the
article and validation record into a new proposal directory rather than
replacing the upstream article. Do not report the proposal as accepted until
its kernel, axiom, dependency, and timing checks pass.

Useful theorem names include:

- `BusyLean.V7.towerOrbit_contender6_lt_contender7`
- `BusyLean.V7.contender_6_lt_contender_7`
- `BusyLean.V7.lower_language_eventually_lt`
- `BusyLean.V7.no_programTree_eq_index`
- `BusyLean.V7.fixed_level_lt_diagonal`

The inherited P5 seed guard is intentionally retained and documented. No
claim is made that every predecessor-related generic definition was removed.
