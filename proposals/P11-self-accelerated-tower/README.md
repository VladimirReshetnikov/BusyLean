# BusyLean Contender 11 research package

## Proposed number

The package proposes a closed Lean natural number built from a
**self-accelerated tower of complete kind-polymorphic forest-reflection rounds**.
In mathematical shorthand, with `B n = F10 (F10 n)` and `R` denoting one full
reflection along BusyLean's self-generated W-tree index,

```text
T_0(n)     = B(n)
T_{k+1}(n) = R(T_k)(T_k(n))
F11(n)     = T_{B(n)+1}(B(n))
C11        = F11(F11(42)).
```

The Lean definitions are in `lean/BusyLean/Contender11.lean`; the formal
comparison theorem proposed for kernel checking is

```lean
theorem contender_10_lt_contender_11 : contender_10 < contender_11
```

in `lean/BusyLean/Comparison11.lean`.

## Why this is a substantial jump

Contender 10 performs one bounded reflection over kind-polymorphic System Fω.
A `round11` instead:

1. exposes a countable family of child stages through the existing computable
   unary pairing code;
2. reflects kind-polymorphic System Fω at every node;
3. traverses `index`, the join of every W-tree denoted by the repository's
   W-language; and
4. repeats that complete operation `B(n)+1` times, self-feeding the previous
   stage's value as the next input.

The exact strict inequality is designed to be kernel-checked. Any
proof-theoretic calibration in the article is explicitly labeled heuristic.

## Package contents

- `article/contender11.tex` - detailed research article.
- `article/contender11.pdf` - compiled article.
- `lean/BusyLean/Contender11.lean` - computable definition.
- `lean/BusyLean/Comparison11.lean` - comparison and structural theorems.
- `lean/test/Contender11Audit.lean` - axiom and dependency-closure audit.
- `lean/scripts/check11.py` - clean-build, time-budget, and axiom checker.
- `integration/` - imports, README text, and a unified patch.
- `notes/` - proof obligations, design alternatives, and provenance.
- `static_audit.py` - conservative source-level check.
- `MANIFEST.sha256` - SHA-256 checksums of packaged files.

## Verification status

The LaTeX source has been compiled and the PDF has been rendered and visually
inspected. The Lean files have passed the bundled source-level audit.

The present execution environment did not contain Lean 4.34.0, so the proposed
Lean modules were **not kernel-checked here**. They deliberately follow the
repository's existing modules and proof patterns, and the package includes the
exact clean-build and audit commands required to complete verification in the
BusyLean checkout. Do not describe the theorem as accepted or kernel-checked
until `python3 scripts/check11.py` passes there.

## Integration and checking

From the BusyLean repository root:

```bash
cp /path/to/package/lean/BusyLean/Contender11.lean BusyLean/
cp /path/to/package/lean/BusyLean/Comparison11.lean BusyLean/
cp /path/to/package/lean/test/Contender11Audit.lean test/
cp /path/to/package/lean/scripts/check11.py scripts/
printf '%s\n' \
  'import BusyLean.Contender11' \
  'import BusyLean.Comparison11' >> BusyLean.lean
python3 scripts/check11.py
```

Alternatively, inspect and apply `integration/contender11.patch`.

## First debugging targets if Lean rejects the draft

The proof is intentionally elementary. The most likely integration issues are
minor elaboration differences around definitional reduction in
`family10_lt_F11`, `fvalue_lt_round11`, or the final `simpa`; the mathematical
argument does not depend on those presentation choices. See
`notes/PROOF_OBLIGATIONS.md` for explicit fallback proof forms.
