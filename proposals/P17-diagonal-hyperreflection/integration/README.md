# Integration notes

This archive is an overlay for the BusyLean repository at baseline commit
`7f6a5c6e44ef31e389b10f6ab6da2bb0284c3502`.

## Automated application

From a clean BusyLean checkout, run:

```bash
/path/to/this/archive/integration/apply_overlay.sh
python3 scripts/check_contender14.py
```

The script copies four Lean modules, the dedicated audit, the checker, and the
GitHub Actions workflow. It idempotently appends the four imports to
`BusyLean.lean`. It does not alter existing contender source files.

## Manual application

Copy these files:

- `overlay/BusyLean/HyperReflection.lean` -> `BusyLean/`
- `overlay/BusyLean/HyperReflectionFacts.lean` -> `BusyLean/`
- `overlay/BusyLean/Contender14.lean` -> `BusyLean/`
- `overlay/BusyLean/Comparison14.lean` -> `BusyLean/`
- `overlay/test/Contender14Audit.lean` -> `test/`
- `overlay/scripts/check_contender14.py` -> `scripts/`
- `overlay/.github/workflows/validate-contender14.yml` -> `.github/workflows/` (optional CI)

Apply `BusyLean.lean.patch`, then run the checker. The optional
`Audit_integration_snippet.lean` can be merged into the repository-wide audit;
the dedicated audit already performs the same new checks.

## Validated branch

The exact code was validated on branch
`research/contender14-diagonal-hyperreflection` at commit
`d408935e8a24da36709886bb08af3439765d05bf` using Lean 4.34.0.
The default branch was not modified by the research process.

Never evaluate `BusyLean.contender_14`.
