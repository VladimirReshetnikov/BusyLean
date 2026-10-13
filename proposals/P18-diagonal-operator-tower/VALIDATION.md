# Validation status

## Completed checks

The proposal was prepared against `VladimirReshetnikov/BusyLean` commit
`1ee50c7d97bbed57a60709f661453c3e213f4db3` (the documented Contender 13
baseline, Lean 4.34.0).

The following checks were completed in the artifact environment:

1. `python3 validation/validate_overlay.py`
   - verified the required definitions and theorem declarations;
   - rejected forbidden source tokens such as `noncomputable`, `partial`,
     `unsafe`, `opaque`, `native_decide`, `sorry`, and new axioms;
   - checked that the executable definition module does not textually depend on
     any closed constant `contender_5` through `contender_13`;
   - checked the exact final equation
     `contender_14 = F14 (F14 42)` and the self-indexed predecessor family;
   - checked basic namespace and delimiter structure;
   - recorded SHA-256 hashes of both Lean modules.

2. Patch preflight
   - `git apply --check contender14.patch` succeeded against a
     baseline-shaped tree containing the exact target contexts.

3. Article and PDF
   - `article/contender14.tex` compiled successfully with `latexmk`/pdfLaTeX;
   - the PDF has 22 letter-size pages and is openable by PyMuPDF;
   - all 22 pages were rendered at 180 dpi and visually inspected in contact
     sheets; no clipping, overlap, missing glyphs, or black boxes were observed;
   - text extraction found the key theorem names and validation caveat.

The detailed command outputs are in `validation/`.

## Mandatory checks not completed here

The environment did not contain Lean 4.34.0 or a materialized BusyLean
checkout. Therefore this archive does **not** claim that:

- Lean elaboration and kernel checking succeeded;
- `#print axioms` reported only `propext` and `Quot.sound`;
- the closure audit excluded all prior closed contender constants;
- the 15-second definition and 60-second proof budgets were met.

These are required integration gates. After applying the patch at the recorded
baseline (or rebasing it), run:

```bash
python3 validation/validate_overlay.py
python3 scripts/check.py
lake env lean test/Audit.lean
```

A clean Lean build should be treated as authoritative. The static checks in this
archive are deliberately not presented as a substitute for kernel validation.
