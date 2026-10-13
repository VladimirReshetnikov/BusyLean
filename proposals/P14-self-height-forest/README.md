# BusyLean Contender 11: self-height diagonal forest closure

This archive proposes a new closed Lean natural number for the BusyLean repository,
pinned to commit `4c4b03d0e2003c479e3bee90a21c8bea13f66c40` and Lean 4.34.0.

The construction combines three amplifiers:

1. **Family-aware kind-polymorphic reflection.** A child family is packed into the unary oracle already supported by Contender 10's object language, while an explicit prefix maximum gives simple child inequalities.
2. **Self-height reflection tower.** At input `n`, the direct reflection value `reflect11 fs n` determines the height `reflect11 fs n + 1` of an iterated `Fk.reflectFk` tower.
3. **W-tree forest closure.** The diagonal node operator is recursively placed along the existing self-indexing tree `index`, then applied twice at 42.

The proposed number is:

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)
def F11 (n : Nat) : Nat := stage11 (fun _ => family10) index n
def contender_11 : Nat := F11 (F11 42)
```

The comparison module contains a proof script for:

```lean
theorem contender_10_lt_contender_11 : contender_10 < contender_11
```

It also proves that each node dominates visible children, bounded kind-polymorphic program values, every reflection tower of height at most the direct reflection value, and the input itself.

## Archive map

- `article/contender11.tex` - detailed research article.
- `article/contender11.pdf` - compiled 20-page article.
- `lean/BusyLean/Contender11.lean` - definitions.
- `lean/BusyLean/Comparison11.lean` - comparison and domination theorems.
- `lean/test/Audit11.lean` - axiom and declaration-closure audit.
- `lean/scripts/check_contender11.py` - clean-build, timing, and audit driver.
- `patches/contender11.patch` - integration patch against the pinned commit.
- `notes/FORMAL_CLAIMS.md` - exact claim/status map.
- `notes/REPRODUCE.md` - replay instructions.
- `validation/` - artifact-level validation logs and scripts.
- `MANIFEST.sha256` - checksums, generated last.

## Verification status

The LaTeX article was compiled, rendered page by page, and visually inspected. Static policy checks, Python syntax checks, PDF checks, and `git apply --check` against a reconstructed pinned-file skeleton passed.

A Lean 4.34.0 executable was not available in the artifact-building environment. Therefore the archive does **not** claim a completed local kernel replay. Run the included checker in the pinned repository before accepting the contender:

```bash
git checkout 4c4b03d0e2003c479e3bee90a21c8bea13f66c40
git apply /path/to/patches/contender11.patch
python3 scripts/check_contender11.py
```

The number is total and computable in principle, but it should never be evaluated directly.
