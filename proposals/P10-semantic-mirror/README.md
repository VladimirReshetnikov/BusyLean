# Semantic Mirror: a proposed BusyLean Contender 7

A model-valued semantic reflection construction extending the **current
Contender 6**, at repository commit
`86b360648163f0249eab79539438b6a83dfe8215`.

**Status: mathematical proof and Lean implementation proposal. New Lean source
has not been compiled.** Python tests and exact upstream-source hash checks
passed. Kernel verification, axiom/dependency audits, and contest timing budgets
remain unexecuted. Read `VALIDATION.md` before treating this as an admitted entry.

## Main result

Let T(0,x)=x, T(h+1,x)=2^T(h,x), and

    B(x) = x + 1 + T(x+1, x+1).

The article proves, uniformly for every natural input n,

    B iterated (n+2) times at BusyLean.finalFamily(n) < Mirror.finalNumber(n).

In particular, the proposed number satisfies

    B iterated 44 times at Contender 6 < Contender 7.

This is a conservative quantitative certificate. Structurally, the new family
also eventually exceeds every fixed program in each finite predecessor
semantic library and is not representable by a single program in any of them.
The final bootstrap also outruns every fixed program in the limit library.

The closed definition is in `lean/BusyLean/Contender7.lean`:

```lean
import Mirror.Model
namespace BusyLean
def contender_7 : Nat := Mirror.finalNumber 42
end BusyLean
```

## Why this is not just a tower around the old winner

A model contains a reflection operator and a tree generator. Its interpreted
library exposes the **entire** hierarchy operator, the tree generator, the
common seed, an input, an independent amplifier, and a relative function family.
The original W-language syntax is unchanged. A fixed ordinary rank-17 program
can construct an older model's full semantic index, run its hierarchy on that
index, and amplify the resulting number. The new reflection maximum exceeds
that program, and every other program within the budget.

A structural recursion on generated W-trees now returns entire models. A
bootstrap traverses the current model's own generated trees. A countable join
collects all finite bootstrap rounds, and one more self-generated bootstrap
is applied. This crosses a sequence of semantic libraries rather than adding
a few arithmetic operations to a completed predecessor constant.

The new number's intended dependency closure excludes `BusyLean.contender_6`,
`BusyLean.finalFamily`, `BusyLean.index`, P5's named contender, and the comparison
witness syntax. Shared **generic** upstream operations and `p5Family` are used;
its inherited old-language maximum guard is retained and disclosed. The formal
closure check is supplied, not executed.

## Files

- `article/semantic_mirror.tex` and `.pdf`: full mathematical report.
- `lean/`: standalone core-only Lean 4.34.0 project, three exact upstream
  dependency files, definition/proof modules, audit, and safe smoke tests.
- `python/`: independent reference interpreter, rank certificates, tests.
- `evidence/`: actual test results, source hashes, unexecuted Lean-check record,
  and PDF verification report.
- `scripts/`: clean Lean verification, source audit, and PDF build utilities.
- `integration/`: optional theorem file and instructions for the complete
  BusyLean repository. Nothing has been pushed or changed in that repository.

## Reproduce

```sh
python3 python/test_reference.py
python3 scripts/source_audit.py
python3 scripts/check_lean.py
python3 scripts/build_pdf.py
```

Lean must be installed separately. Alternatively, inside `lean/`, `lake build`
checks the library; then `lake env lean Mirror/Audit.lean` runs the explicit
audits. The direct checker above is preferred for clean phase timing.

**Never evaluate the contender, a concrete semantic model number, or a program
maximum.** Definitions and comparison proofs are intended to be checked without
computing either giant number. The Python tests do not evaluate the entry.

## Scope

The primary exact target is C6. C5 and P5 follow by transitivity using the
upstream proofs. No separate machine-checked P1-P4 ranking, absolute maximality,
standard ordinal calibration, or literature-priority claim is made. The new
number is computable in principle by explicitly total operations; actual Lean
acceptance and contest eligibility still require the external checks above.
