# Build and validation status

## Completed in the packaging environment

- Audited the current BusyLean baseline at commit
  `64d31a0cf6f1aa4477a088be5554957de6e87a61`.
- Matched the repository's pinned toolchain declaration:
  `leanprover/lean4:v4.34.0`.
- Wrote the definition, comparison, audit, and build-harness sources.
- Ran `artifacts/static_audit.py`: **PASS**.
- Checked every library-source line is at most 100 columns.
- Compiled the LaTeX article with `latexmk -pdf`.
- Rendered every PDF page and visually inspected the rendered output.
- Generated the patch, diagrams, hashes, and ZIP archive.

## Not available in this environment

Neither `lean` nor `lake` was installed, and no Lean kernel replay was
performed.  Therefore this package intentionally makes no claim that:

- the Lean sources elaborate without a repair;
- `#print axioms` is restricted to `propext` and `Quot.sound`;
- the transitive closure of `contender_20` avoids the earlier contender
  constants; or
- the 15-second definition and 60-second proof budgets are met.

These are concrete, automated pending checks rather than informal omissions.
After installation, run:

```bash
python3 scripts/check20.py
```

The harness cleans build directories, builds `BusyLean.Comparison19` as the
accepted baseline, times `BusyLean.Contender20` and `BusyLean.Comparison20`,
and runs `test/Audit20.lean`.

## Confidence assessment

The proof design reuses the accepted signatures of `stageLift`,
`base_lt_stageLift`, `diagonalLift_preservesProgressive`, and
`diagonalLift_strictlyInflationary`.  It follows the repository's existing
explicit-coordinate proof style and introduces no semantic monotonicity
assumption.  Nevertheless, only actual Lean 4.34.0 replay can establish formal
acceptance.
