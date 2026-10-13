# Integration patches

- `contender14_new_files.patch` adds the two Lean modules, the dedicated audit,
  and the clean-build harness.
- `BusyLean.lean.patch` adds the new modules to the aggregate import file.
- `Audit14.patch` extends the repository-wide audit.
- `check.py.patch` advances the repository's current-contender timing harness.

Apply from the root of the BusyLean checkout:

```bash
git apply /path/to/contender14_new_files.patch
git apply /path/to/BusyLean.lean.patch
git apply /path/to/Audit14.patch
git apply /path/to/check.py.patch
```

Alternatively, copy the files directly as described in the package root
`README.md`.
