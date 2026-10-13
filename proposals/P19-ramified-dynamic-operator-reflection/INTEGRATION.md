# Integration and acceptance procedure

## Baseline

This overlay was prepared against:

```text
repository: VladimirReshetnikov/BusyLean
commit:     1ee50c7d97bbed57a60709f661453c3e213f4db3
toolchain:  leanprover/lean4:v4.34.0
```

Use that exact commit for the first acceptance run.  Later repository versions
may require conflict resolution even when the mathematics is unchanged.

## Method A: overlay installer

```bash
unzip BusyLean_Contender14_RDOR.zip
cd BusyLean_Contender14_RDOR
./scripts/apply_overlay.sh /absolute/path/to/BusyLean
cd /absolute/path/to/BusyLean
python3 scripts/check.py
lake env lean test/Contender14Audit.lean
```

The installer is idempotent.  It performs the following changes:

1. copies `BusyLean/Contender14.lean` and `BusyLean/Comparison14.lean`;
2. copies `test/Contender14Audit.lean`;
3. copies the article as `article/contender14_rdor.{tex,pdf}`;
4. appends `Contender14` and `Comparison14` imports to `BusyLean.lean`;
5. changes the timing harness to
   `PREVIOUS = "BusyLean.Comparison13"` and
   `CURRENT_DEF = "BusyLean.Contender14"`;
6. appends the Contender-14 axiom and dependency-closure audit once.

## Method B: unified patch

From a clean checkout at the baseline commit:

```bash
git apply --check /path/to/BusyLean_Contender14_RDOR/patches/integration.patch
git apply /path/to/BusyLean_Contender14_RDOR/patches/integration.patch
python3 scripts/check.py
lake env lean test/Contender14Audit.lean
```

The patch intentionally excludes rendered diagnostic PNGs and package-level
metadata.  It installs only repository-facing sources, tests, article files,
and harness updates.

## Required acceptance checks

### 1. Definition budget

The repository harness should build the accepted previous contender first,
then time `BusyLean.Contender14` against the 15-second definition budget.
Record the exact wall-clock result and hardware.

### 2. Proof budget

The remaining library, including `BusyLean.Comparison14`, should fit the
60-second proof budget.  Record the clean-build total as well.

### 3. Kernel and axiom audit

The output must show that the new declarations use only the axioms permitted by
BusyLean (`propext` and `Quot.sound`, allowing consequences such as `funext`).
Any `sorryAx`, `Classical.choice`, custom axiom, or unexpected dependency is a
hard failure.

### 4. Dependency closure

The integrated `#assert_not_in_closure` check must show that
`BusyLean.contender_14` does not depend on any predecessor contender constant.
It may depend on predecessor **constructions**, notably `F13`, `family12`, the
`Fd` normalizer, `operatorStage`, and the autonomous tree machinery; this is the
intended admissible reuse.

### 5. Do not evaluate the contender

No acceptance command should contain `#eval BusyLean.contender_14` or otherwise
force normalization of `F14 42`.  The comparison is symbolic and structural.

## Recommended receipt

Copy `BUILD_RECEIPT_TEMPLATE.md`, fill every field, paste unedited command
output, and save it beside the integrated proposal.  A complete receipt should
contain:

- repository commit before and after applying the overlay;
- `lean --version` and `lake --version`;
- operating system, CPU, memory, and filesystem notes;
- clean definition, proof, and total times;
- complete axiom reports;
- dependency-closure result;
- exit status of both required commands;
- SHA-256 hashes of the two Lean modules.

## Troubleshooting priorities

1. Confirm the baseline commit and toolchain pin before editing proofs.
2. If a `change` command fails due to elaboration, replace it with explicit
   `unfold`/`rfl` steps without changing definitions.
3. If timing exceeds the budget, profile elaboration before weakening the
   construction; likely hotspots are numeral reduction in the explicit margin
   theorem and repeated unfolding of `operatorTower`.
4. Do not replace proof terms with `native_decide`, `simp?` output that imports
   forbidden axioms, or opaque shortcuts.
