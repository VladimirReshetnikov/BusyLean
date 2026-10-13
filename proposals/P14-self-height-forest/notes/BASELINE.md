# Baseline provenance

- Repository: `VladimirReshetnikov/BusyLean`
- Pinned commit: `4c4b03d0e2003c479e3bee90a21c8bea13f66c40`
- Target toolchain: Lean 4.34.0
- Incumbent: `BusyLean.contender_10`

Relevant baseline modules:

- `BusyLean/Contender9.lean`: `packFamily`, `stage9`, and W-tree forest reflection.
- `BusyLean/Comparison9.lean`: pairing correctness and forest comparison pattern.
- `BusyLean/Contender10.lean`: kind-polymorphic program enumeration, `Fk.fvalue`, `Fk.reflectFk`, `F10`, and `contender_10`.
- `BusyLean/Comparison10.lean`: `Fk.oracle_lt_reflectFk`, `Fk.input_lt_reflectFk`, and the incumbent comparison.
- `BusyLean/Contender6.lean`: `defTree`, `treesOfDepth`, and `index`.
- `test/Audit.lean`: accepted axiom and declaration-closure audit pattern.
- `scripts/check.py`: accepted phase timing and audit driver pattern.

The integration patch is generated against the exact `BusyLean.lean` contents at the pinned commit. New modules import the incumbent modules rather than copying their internal metatheory.
