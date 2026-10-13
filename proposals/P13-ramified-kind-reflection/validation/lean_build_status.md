# Lean kernel-build status

**Status: NOT RUN in the preparation environment.**

The target repository pins `leanprover/lean4:v4.34.0`. No `lean`, `lake`, or
`elan` executable was installed in the working container, and attempts to
obtain the toolchain were blocked by the environment's external download
constraints. Consequently:

- `BusyLean/Contender11.lean` has not been elaborated or kernel-checked here;
- `BusyLean/Comparison11.lean` has not been elaborated or kernel-checked here;
- `#print axioms` and dependency-closure results have not been produced by
  Lean here;
- the 15-second definition and 60-second proof budgets have not been measured.

Completed substitute checks, which are useful but not authoritative:

1. a source audit excluding forbidden declaration forms and direct use of any
   earlier contender constant in the executable definition;
2. delimiter, declaration-presence, line-length, and hash checks;
3. a finite executable reference model with five regression tests;
4. patch application and installer idempotency tests;
5. successful three-pass LuaLaTeX compilation, 23-page rendering, text
   extraction, and visual inspection.

Authoritative acceptance command after integration into the recorded BusyLean
snapshot:

```bash
python3 scripts/check_contender11.py
```

The supplied harness clean-builds Contender 10 as the accepted predecessor,
times the new definition and proof phases, runs the standalone audit, and
rejects axioms beyond `propext` and `Quot.sound`.
