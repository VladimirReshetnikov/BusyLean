# Reproducing and checking Contender 11

## 1. Prepare the exact repository state

```bash
git clone https://github.com/VladimirReshetnikov/BusyLean.git
cd BusyLean
git checkout 4c4b03d0e2003c479e3bee90a21c8bea13f66c40
```

Confirm that `lean-toolchain` names Lean 4.34.0.

## 2. Apply the patch

From the BusyLean repository root:

```bash
git apply /absolute/path/to/BusyLean_Contender11_DiagonalForest/patches/contender11.patch
```

The patch:

- adds `BusyLean/Contender11.lean`;
- adds `BusyLean/Comparison11.lean`;
- adds `test/Audit11.lean`;
- adds `scripts/check_contender11.py`; and
- imports the two new modules from `BusyLean.lean`.

The same source files are also supplied separately under this archive's `lean/` directory for review.

## 3. Run the acceptance-oriented checker

With `elan`, Lean 4.34.0, and `lake` available:

```bash
python3 scripts/check_contender11.py
```

The script deletes build directories and performs three phases:

1. builds `BusyLean.Comparison10` as accepted history, outside the new budget;
2. builds `BusyLean.Contender11` with a 15-second definition budget;
3. builds the remaining library with a 60-second proof budget.

It then runs:

```bash
lake env lean test/Audit11.lean
```

The audit prints axiom dependencies and checks that `BusyLean.contender_11` does not depend on any closed contender constant from `contender_10` through `contender_5`. The Python driver rejects axioms other than `propext` and `Quot.sound`.

## 4. Useful focused commands

```bash
lake build BusyLean.Contender11
lake build BusyLean.Comparison11
lake env lean test/Audit11.lean
```

Do not use `#eval BusyLean.contender_11` and do not attempt to reduce the number.

## 5. Compile the article

```bash
cd /path/to/BusyLean_Contender11_DiagonalForest/article
pdflatex -interaction=nonstopmode -halt-on-error contender11.tex
pdflatex -interaction=nonstopmode -halt-on-error contender11.tex
pdflatex -interaction=nonstopmode -halt-on-error contender11.tex
```

Render for visual inspection:

```bash
python /home/oai/skills/pdfs/scripts/render_pdf.py \
  contender11.pdf --out_dir /tmp/contender11-render --dpi 170
```

## 6. Expected central declarations

```lean
#check @BusyLean.family10_lt_F11
#check @BusyLean.fixedTower_lt_diagonal11
#check @BusyLean.defined_tree_eventually_lt11
#check @BusyLean.contender_10_lt_contender_11
```

A successful replay is the final acceptance criterion. Static checks in this archive are not a substitute for Lean kernel checking.
