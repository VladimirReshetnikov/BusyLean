# BusyLean Contender 14 research package

## Proposal

**Contender 14: Bi-Diagonal Rank Reflection over Dynamic-Kind System Fω**

The construction upgrades Contender 13 in three ways:

1. Dynamic-kind System Fω receives a computably packed countable oracle family.
2. Reflection is lifted to a strictly increasing hierarchy of meta-transformers.
3. Both the meta-rank and autonomous schedule rank at input `n` are
   `family13 n + 1`, after which the complete ranked family is reflected once
   more.

The proposed closed number is:

```lean
def contender_14 : Nat := F14 (F14 42)
```

The comparison source proves the pointwise theorem
`family13 n < F14 n`, then derives
`contender_13 < contender_14`.

## Audited baseline

- Repository: `VladimirReshetnikov/BusyLean`
- Commit: `1ee50c7d97bbed57a60709f661453c3e213f4db3`
- Pinned toolchain: `leanprover/lean4:v4.34.0`
- Audit date: October 12, 2026 in America/Los_Angeles
- The audited HEAD is a documentation-only child of code commit `7f6a5c6e44ef31e389b10f6ab6da2bb0284c3502`; the relevant Lean blobs are unchanged.

The baseline already contains Contenders 12 and 13. This package targets
Contender 13, not the older Contender 11 proposals in `incoming/`.

## Package contents

- `article/contender14.tex` — 23-page research article.
- `article/contender14.pdf` — compiled and visually inspected PDF.
- `overlay/BusyLean/HyperReflection.lean` — generic meta-reflection hierarchy.
- `overlay/BusyLean/Contender14.lean` — definitions of the new family and number.
- `overlay/BusyLean/Comparison14.lean` — strict comparison and program bounds.
- `overlay/test/Audit14.lean` — axiom and transitive-dependency audit.
- `overlay/scripts/check14.py` — clean-build timing and audit harness.
- `install.sh` — idempotent overlay installer.
- `busylean-contender14.patch` — equivalent unified patch.
- `artifacts/static_audit.py` and reports — source-level checks.
- `artifacts/claim_matrix.csv` — claim/evidence/qualification table.
- `artifacts/contender_comparison.csv` — architectural comparison of C5–C14.
- `artifacts/dependency_graph.*` — machine-readable and rendered dependency graph.
- `artifacts/pdf_contact_sheet.png` — all 23 rendered pages for compact visual review.
- `source_audit/baseline.json` — audited commit and source hashes.
- `MANIFEST.sha256` — package integrity manifest.

## Install and validate

From the unpacked package:

```bash
./install.sh /path/to/BusyLean
cd /path/to/BusyLean
python3 scripts/check14.py
```

For a non-audited or modified checkout, review the patch before installation.
Use `--force` only when intentionally replacing existing overlay files.

The build harness performs these phases from deleted build directories:

1. Build `BusyLean.Comparison13` as the accepted baseline.
2. Build `BusyLean.Contender14` against the 15-second definition budget.
3. Build `BusyLean.Comparison14` against the 60-second proof budget.
4. Run the repository audit and the focused Contender 14 audit.
5. Reject any axiom outside `propext` and `Quot.sound`.

## Validation status

The LaTeX article compiles, the resulting PDF was rendered page by page and
visually inspected, and the included static source audit passes. The sandbox
used to create this package did not contain Lean or Lake, so **Lean kernel
replay and timing measurements have not been claimed**. The provided harness is
the required final acceptance step in a checkout with Lean 4.34.0 available.

## Mathematical highlights

- `rankLift_step_lt` makes every successor meta-rank strictly exceed the
  preceding rank at canonical coordinate zero.
- `fixed_rank_lt_diagonalRank14` shows the previous-number-controlled rank
  eventually exceeds every fixed finite rank.
- `family13_lt_F14` proves pointwise domination of the full Contender 13 family.
- `fvalue_lt_F14` proves that every enumerated dynamic-kind program in the final
  reflection layer is below `F14 n` relative to the packed ranked oracle.
- The proof never assumes semantic monotonicity in an oracle; all comparisons
  come from explicit finite maxima and generic progressivity lemmas.
