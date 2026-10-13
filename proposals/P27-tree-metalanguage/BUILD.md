# Build and verification instructions

## Target environment

- Repository: `VladimirReshetnikov/BusyLean`
- Baseline commit used for this proposal: `43513401d8929d60b2e3e40a4a20835a1271e94f`
- Lean toolchain: `leanprover/lean4:v4.34.0`
- Proposal verification branch: `research/contender35-metalanguage-20261013`

## Install into an existing checkout

From this archive's root:

```bash
./apply_to_checkout.sh /path/to/BusyLean
```

The script copies the three source modules and the isolated audit, then appends
three imports to `BusyLean.lean` if they are absent.

## Kernel-check only the new modules

```bash
cd /path/to/BusyLean
lake build BusyLean.Ordinal.TreeLanguage4
lake build BusyLean.Contender35
lake build BusyLean.Comparison35
lake env lean test/Contender35Audit.lean
```

## Full build

```bash
lake build
```

## Important

Do **not** use `#eval`, `#reduce`, `#print` with value unfolding, or an executable
entry point on `BusyLean.contender_35`.  The definition is computable in
principle, but evaluating the represented natural is deliberately infeasible.
