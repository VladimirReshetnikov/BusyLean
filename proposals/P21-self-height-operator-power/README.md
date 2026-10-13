# BusyLean Contender 14 research package

## Proposed number

```lean
def contender_14 : Nat := F14 (F14 42)
```

`F14 n` is a self-height finite tower of complete operator-reflection stages.
The base step is dynamic-kind System F-omega reflection lifted to countable
oracle families. The tower has `family13 n + 1` levels, is seeded by the full
Contender 13 family, and is evaluated at `family13 n`.

The supplied comparison module targets the pointwise theorem

```lean
theorem family13_lt_F14 (n : Nat) : family13 n < F14 n
```

and then the required closed comparison

```lean
theorem contender_13_lt_contender_14 : contender_13 < contender_14
```

## Contents

- `BusyLean/Contender14.lean` - transparent executable definitions.
- `BusyLean/Comparison14.lean` - strict comparison and structural margins.
- `test/Audit14.lean` - axiom and forbidden-dependency audit.
- `scripts/check14.py` - clean build and timing harness.
- `scripts/static_audit.py` - fast source-level audit.
- `integration/` - ready-to-apply patches and integration instructions.
- `article/contender14_self_height_fd_operator_power.tex` - article source.
- `article/contender14_self_height_fd_operator_power.pdf` - compiled article.
- `article/BUILD_NOTES.md` - PDF build and inspection record.
- `design/DEPENDENCY_GRAPH.md` - construction and proof dependency graph.
- `notes/FORMAL_CLAIMS.md` - inventory of intended kernel-checked claims.
- `source_snapshot.json` - exact upstream snapshot metadata.
- `VALIDATION.md` - exact validation status and limitation.
- `MANIFEST.sha256` - integrity hashes.

## Integration

From a BusyLean checkout at or after commit
`0cd13c0c2607b4fcb461090a95f356e538c0fc5b`, either apply the patches under
`integration/` or copy the overlay files:

```bash
cp BusyLean/Contender14.lean /path/to/BusyLean/BusyLean/
cp BusyLean/Comparison14.lean /path/to/BusyLean/BusyLean/
cp test/Audit14.lean /path/to/BusyLean/test/
cp scripts/check14.py /path/to/BusyLean/scripts/
cd /path/to/BusyLean
python3 scripts/check14.py
```

The definition file never mentions any earlier `contender_N` constant. It uses
`family13`, built from `F13`, as the seed and self-height parameter of a
qualitatively stronger operator construction, as permitted by the contest
rules.

## Validation caveat

The article and source audits were completed in the package-building
container. The Lean overlay could not be kernel-compiled there because the
pinned Lean 4.34.0 toolchain was unavailable. See `VALIDATION.md` for the exact
status and the included reproducibility checks.
