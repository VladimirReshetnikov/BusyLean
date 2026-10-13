# BusyLean Contender 11 proposal

## Crowned kind-polymorphic forest reflection

This package proposes a new closed Lean natural number for
[`VladimirReshetnikov/BusyLean`](https://github.com/VladimirReshetnikov/BusyLean),
pinned to commit `4c4b03d0e2003c479e3bee90a21c8bea13f66c40`.
At that revision the incumbent is Contender 10, based on kind-polymorphic
System F-omega.

The proposal is:

```lean
def family10 (n : Nat) : Nat := F10 (F10 n)

def F11 (n : Nat) : Nat :=
  stage11 (fun _ => family10) (crown11 (n + 1) index) n

def contender_11 : Nat := F11 (F11 42)
```

`stage11` installs the Contender 10 kind-polymorphic reflector at every node of
a well-founded `WTree Nat`.  The base tree is BusyLean's self-generated index
of all trees denoted by its earlier W-language.  `crown11 (n + 1)` places an
input-diagonal chain of additional reflection nodes above that index.

The supplied proof module states and proves, in Lean source:

```lean
theorem family10_lt_F11 (n : Nat) : family10 n < F11 n

theorem contender_10_lt_contender_11 :
  contender_10 < contender_11
```

It also gives exact structural margins:

- every visible child is below its parent reflection node;
- every accepted depth-bounded kind-polymorphic program is below the root;
- every crown step is strict;
- every W-language-defined tree is eventually below `F11`.

## Validation status

**The Lean kernel run is not claimed complete.**  The packaging environment did
not contain `lake` or Lean 4.34.0.  The receipt in
`evidence/lean_validation.json` therefore says `not_run`.

Completed checks:

- static audit of the four new Lean files: passed;
- executable definition syntax does not reference the named scalar
  `contender_10`: passed;
- forbidden escape-hatch token scan: passed;
- independent finite structural model: 670 assertions passed;
- LaTeX build: passed, 22 pages;
- PDF render and visual inspection: passed;
- package hash manifest: included.

The automated kernel/timing runner is `scripts/check_in_repo.py`.  A successful
run under the pinned toolchain is required before this can be described as an
accepted BusyLean contender.

## Package map

- `article/contender11.tex`, `article/contender11.pdf` — research article.
- `candidate/BusyLean/Contender11.lean` — computational definition.
- `candidate/BusyLean/Comparison11.lean` — comparison and structural proofs.
- `candidate/test/Audit11.lean` — axiom and transitive closure audit.
- `candidate/test/Contender11Smoke.lean` — non-evaluating definitional tests.
- `integration/install.py` — pinned, dry-run-first integration helper.
- `integration/0001-contender11.patch` — additive Git patch.
- `scripts/check_in_repo.py` — Lean build, timing, axiom, and closure runner.
- `scripts/static_audit.py` — source hygiene audit.
- `scripts/reference_model.py` — finite independent model.
- `docs/VALIDATION_BOUNDARY.md` — exact trust boundary.
- `evidence/` — machine-readable receipts and build logs.

## Reproduction

First review the integration plan:

```bash
python3 integration/install.py /path/to/BusyLean
```

Apply it after review:

```bash
python3 integration/install.py /path/to/BusyLean --apply
python3 scripts/check_in_repo.py /path/to/BusyLean
```

The checker builds the accepted predecessor first, then times the new
definition and proof modules against the repository's 15-second and 60-second
budgets.  It never evaluates a contender.

Re-run package-local checks:

```bash
python3 scripts/static_audit.py
python3 scripts/reference_model.py
cd article
pdflatex -interaction=nonstopmode -halt-on-error contender11.tex
pdflatex -interaction=nonstopmode -halt-on-error contender11.tex
pdflatex -interaction=nonstopmode -halt-on-error contender11.tex
```

## Central mathematical chain

Let `s i n = family10 n`.  The old self-generated index contains a leaf along
the path `index -> treesOfDepth 0 -> leaf`.  Since every forest parent exceeds
each visible child,

```text
family10 n
  < stage11 s leaf n
  < stage11 s (treesOfDepth 0) n
  < stage11 s index n
  < stage11 s (crown11 (n + 1) index) n
  = F11 n.
```

At `n = 42`, `family10 42` is definitionally `contender_10`.  Every stage also
exceeds its numerical input, so

```text
contender_10 < F11 42 < F11 (F11 42) = contender_11.
```

No numerical normalization or conjectural ordinal estimate is used.
