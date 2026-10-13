# BusyLean Contender 14 research package

## Ramified Dynamic Operator Reflection (RDOR)

This archive proposes a new closed computable Lean natural number for the
BusyLean contest, based on repository commit
`1ee50c7d97bbed57a60709f661453c3e213f4db3` and its pinned toolchain
`leanprover/lean4:v4.34.0`.

The proposal is deliberately an **overlay**, not a replacement repository.  It
contains two new Lean modules, audit and integration material, a detailed
LaTeX article and compiled PDF, a construction diagram, and reproducibility
metadata.

## Definition

The base reflection step upgrades Contender 13's unary dynamic-kind oracle to a
packed countable family:

```lean
def reflectFdFamily (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN
    (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fd.fvalue (packFamily fs) n) (Fd.ctmsUpTo n))
```

It is packaged as a progressive transformer and then fed through a strict
operator-level feedback construction:

```lean
def towerStep (base : Transformer) : Transformer :=
  fun seed => (operatorStage base tree14) (base seed)

def operatorTower : Nat → Transformer
  | 0 => fdFamilyTransformer
  | k + 1 => towerStep (operatorTower k)
```

The predecessor construction is exposed as a function, never by using the
constant `contender_13` in the executable dependency closure:

```lean
def family13 (n : Nat) : Nat := F13 (F13 n)
def iterateF13 : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => F13 (iterateF13 k n)
def seed13 : W.Family := fun i n => iterateF13 i (family13 n)
```

The proposed number is

```lean
def F14 (n : Nat) : Nat :=
  operatorTower (n + 1) seed13 n n

def contender_14 : Nat := F14 (F14 42)
```

All recursions are structural.  The executable source contains no
`noncomputable`, `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`,
`native_decide`, `sorry`, custom axiom, or unbounded search.

## Formal claims encoded in the overlay

`BusyLean/Comparison14.lean` contains proofs intended to establish:

- family-aware dynamic-kind reflection exceeds every visible oracle-family
  coordinate and every accepted bounded dynamic-kind program;
- the base transformer is progressive;
- `towerStep` preserves progressivity and strictly dominates its base;
- every level of `operatorTower` is progressive and the levels form a strict
  pointwise chain;
- `family13 n < F14 n` and `n < F14 n` for every `n`;
- `contender_13 < contender_14`;
- the stronger exact lower bound
  `iterateF13 42 contender_13 < F14 42`, equivalently the numerical chain
  described in the article as `F13^[44](42) < F14 42 < contender_14`;
- every accepted `Fd` program at the relevant budget, using `seed13` as its
  packed oracle family, is below `F14` and hence below `contender_14` at the
  outer budget.

The construction is therefore not an arithmetic post-composition of the old
constant.  It lifts the current dynamic-kind reflection mechanism to families,
feeds an entire transformer output back through an autonomous operator stage,
and repeats that strict meta-step an input-dependent number of times.

## Archive map

| Path | Purpose |
|---|---|
| `BusyLean/Contender14.lean` | Executable definitions of the proposed family and number |
| `BusyLean/Comparison14.lean` | Progressivity, comparison, large-margin, and program bounds |
| `test/Contender14Audit.lean` | Standalone `#print axioms` / `#check` audit |
| `patches/Audit14.append.lean` | Block to append to BusyLean's existing dependency audit |
| `patches/integration.patch` | Unified patch for a checkout at the recorded base commit |
| `scripts/apply_overlay.sh` | Idempotent overlay installer |
| `scripts/check_in_repo.sh` | Runs the repository checks after integration |
| `scripts/static_audit.py` | Source-level preflight; explicitly not a kernel check |
| `article/contender14_rdor.tex` | Full research article |
| `article/contender14_rdor.pdf` | Compiled 17-page article |
| `artifacts/construction_graph.{dot,svg,png}` | Construction and proof dependency diagram |
| `artifacts/static_audit.txt` | Preflight output and source hashes |
| `artifacts/pdf_inspection.txt` | PDF metadata, font, text, and rendering checks |
| `VERIFICATION_STATUS.md` | Precise statement of completed and pending verification |
| `INTEGRATION.md` | Integration and acceptance procedure |
| `DESIGN_SUMMARY.md` | Mathematical and engineering rationale |
| `BUILD_RECEIPT_TEMPLATE.md` | Template for the required pinned Lean build receipt |
| `MANIFEST.json`, `SHA256SUMS.txt` | Machine-readable inventory and integrity hashes |

## Quick integration

From this archive:

```bash
./scripts/apply_overlay.sh /path/to/BusyLean
cd /path/to/BusyLean
python3 scripts/check.py
lake env lean test/Contender14Audit.lean
```

The installer checks the repository shape, copies the new modules and article,
adds root imports, advances the timing harness from Contender 13 to Contender
14, and appends the dependency-closure audit exactly once.

## Verification status

The LaTeX article compiles cleanly and the rendered PDF has been visually
inspected.  The static source audit passes, and the archive includes hashes and
a reproducible integration route.

The preparation container did **not** contain Lean 4.34.0 or `lake`, and its
runtime network could not install the pinned toolchain.  Consequently, this
archive does not pretend to contain a Lean-kernel acceptance receipt.  The
remaining acceptance step is the clean pinned build and axiom/dependency audit
described in `VERIFICATION_STATUS.md` and `BUILD_RECEIPT_TEMPLATE.md`.
