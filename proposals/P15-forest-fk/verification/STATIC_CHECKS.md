# Local static and artifact checks

Recorded on 12 October 2026.

- `python -m py_compile scripts/check_contender11.py scripts/verify_axle.py`: PASS.
- Forbidden construction-token scan over `BusyLean/*.lean` for
  `noncomputable`, `partial`, `unsafe`, `opaque`, `axiom`, `sorry`, and
  `admit`: no matches.
- Predecessor-constant scan over `BusyLean/Contender11.lean` for
  `contender_5` through `contender_10`: no matches.
- `patches/0001-contender11.patch`: `git apply --check` and a full test apply
  against the pinned `BusyLean.lean` baseline both passed.
- PDF preflight: 14 pages, openable, unencrypted, embedded fonts, no forms,
  no JavaScript, and not image-only.
- PDF render review: all 14 pages rendered and inspected; no clipped text,
  overlaps, broken glyphs, or black boxes were observed.

These checks complement, but do not replace, Lean elaboration/kernel checking
and the staged Lake build described in `AXLE_REPORT.md` and
`integration/INTEGRATION.md`.
