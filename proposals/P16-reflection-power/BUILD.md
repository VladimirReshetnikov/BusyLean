# Integration and build instructions

The overlay targets BusyLean commit
`86b360648163f0249eab79539438b6a83dfe8215` and its pinned toolchain
`leanprover/lean4:v4.34.0`.

From a clean checkout of that commit:

```bash
cp /path/to/package/lean/BusyLean/Contender7.lean BusyLean/
cp /path/to/package/lean/BusyLean/Comparison7.lean BusyLean/
cat /path/to/package/lean/BusyLean.lean.append >> BusyLean.lean
cp /path/to/package/lean/test/Contender7Audit.lean test/
rm -rf .lake
lake build
lake env lean test/Contender7Audit.lean
```

For a repository-integrated CI job, copy `ci/contender7.yml` to
`.github/workflows/contender7.yml` and copy the package scripts to `scripts/`.

The local, non-kernel checks are:

```bash
./scripts/run_checks.sh
```

Do not evaluate `BusyLean.contender_7`.
