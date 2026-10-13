# BusyLean Contender 20 overlay

This package proposes **Contender 20: W-rank hyperreflection** for BusyLean.
It is an overlay against commit
`64d31a0cf6f1aa4477a088be5554957de6e87a61` (2026-10-13).

## Main definition

```lean
def family19 (n : Nat) : Nat := F19 (F19 n)

def seedLift20 (n : Nat) : TransformerLift :=
  diagonalLift (schedule20 n) (family19 n + 1)

def lift20 (n : Nat) : TransformerLift :=
  treeDiagonalLift (schedule20 n) (rankTree20 n) (seedLift20 n)

def F20 (n : Nat) : Nat :=
  lift20 n lTransformer seedFamily20 n n

def contender_20 : Nat := F20 (F20 42)
```

The new ingredient is `treeDiagonalLift`.  It raises the finite rank hierarchy
of `diagonalLift` one type level: transformer lifts are recursively spliced and
amplified along a countably branching well-founded `WTree Nat`.

The formal comparison chain is pointwise:

```text
family19 n
  < raw large-Veblen reflection
  < the finite-rank seed lift
  < the W-rank lift = F20 n.
```

Hence `contender_19 < contender_20`.

## Files

- `BusyLean/TransfiniteHyperReflection.lean`: generic second-order machinery.
- `BusyLean/Contender20.lean`: schedules and the number.
- `BusyLean/Comparison20.lean`: strict-growth and comparison theorems.
- `test/Audit20.lean`: axiom and dependency-closure audit.
- `test/Contender20Smoke.lean`: non-evaluating smoke checks.
- `scripts/static_audit.py`: compiler-independent token and delimiter checks.
- `scripts/build_overlay.sh`: intended Lean build/audit commands.
- `article/contender20.tex` and `article/contender20.pdf`: research note.
- `integration/contender20.patch`: apply-ready source overlay and budget-script update.
- `artifacts/architecture.{dot,svg,png}`: construction and dependency diagram.
- `VERIFICATION.md` and `BUILD_STATUS.md`: precise evidence and verification boundary.
- `MANIFEST.sha256`: archive integrity manifest.

## Integration

Copy the package's `BusyLean/` and `test/` files into the repository, append
`integration/BusyLean.lean.append` to `BusyLean.lean`, and run:

```bash
python3 scripts/static_audit.py
lake build BusyLean.Contender20
lake build BusyLean.Comparison20
lake env lean test/Contender20Smoke.lean
lake env lean test/Audit20.lean
```

Do not evaluate `contender_20`, `F20 42`, or any nontrivial predecessor.

## Verification status

The package includes a complete Lean proof design and a static audit.  The
current artifact environment did not contain a Lean executable, so the Lean
sources could not be kernel-checked here.  They are written specifically for
the repository's declared Lean 4.34.0 toolchain and reuse the established proof
interfaces from `HyperReflectionFacts` and `Comparison19`.
