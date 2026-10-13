# Constructive Reflection Beyond Contender 5

**A checked Lean 4 large-number entry, with its research article and reproducible validation.**

This package adapts Cody Roux's [name-the-biggest-number contest](https://github.com/codyroux/name-the-biggest-number) from Coq to Lean. It defines a closed, constructive natural number named `contender_6` and proves the fixed-input comparison

```lean
theorem contender_5_lt_contender_6 :
    Original.contender5 < contender_6
```

`Original.contender5` faithfully ports the computational definition of the repository's fifth contender, including its evaluation of malformed raw terms. The final entry uses structural tree recursion, finite-program reflection, and an accessible family of function oracles. Its numerical definition does not refer to the named previous-contender constant.

Start with [the compiled article](article/article.pdf) for the mathematical development, or [Contender.lean](lean/Contender.lean) for the final definition and its comparison theorems. The [article source](article/article.tex) contains the proofs, scope qualifications, references, and further research questions.

**Do not normalize the final number.** In particular, do not run `#eval contender_6`, `#reduce contender_6`, or evaluations of Contender 5 and the large reflection stages. Verification checks their definitions and comparison proofs without expanding their values. The supplied scripts perform only explicitly small semantic evaluations.

## Reproduce the Lean verification

### Requirements

- The normal **Lean 4.19.0** distribution and its standard library. The included `lean-toolchain` pins `leanprover/lean4:v4.19.0`.
- Python 3 with its standard library and a `python3` executable on `PATH`. The verifier also uses that command to launch the independent reference model. The recorded run used Python 3.12.14.
- **No Mathlib, Coq installation, third-party Python packages, or project dependency downloads are needed** once the pinned Lean distribution is installed.

Run the following from the extracted archive's root directory. With an elan-managed installation:

```bash
lean --version
python3 scripts/verify.py --lean "$(elan which lean)" \
  --output validation/reproduced/build_report.json
```

`--lean` should name the **actual compiler binary**. The verifier compiles inside a fresh temporary directory; resolving the real binary from the archive root prevents that build from depending on elan's default toolchain outside this directory. With a directly installed distribution, provide its absolute path instead:

```bash
python3 scripts/verify.py \
  --lean /absolute/path/to/lean-4.19.0-linux/bin/lean \
  --output validation/reproduced/build_report.json
```

The verifier itself does not require Bash. For example, the elan command in Windows PowerShell is:

```powershell
python3 scripts/verify.py --lean (elan which lean) --output validation/reproduced/build_report.json
```

The script rejects a compiler whose reported version is not 4.19.0. It then:

1. Copies all eleven delivered Lean modules into a fresh temporary project.
2. Checks and compiles every module in dependency order, rebuilding all project imports while reusing only the installed Lean standard library.
3. Runs the explicit axiom audit and requires all 288 reports to be present and empty.
4. Traverses the elaborated dependency graph of the final numerical definition.
5. Compares every original-program evaluation through depth four with an independent Python reference model.

Successful output reports `"status": "PASS"` and an axiom audit with `"targets": 288`, `"empty_axiom_lists": 288`, and `"all_empty": true`. With the commands above, the new build report, `lean_build.log`, and `source_crosscheck.json` appear under `validation/reproduced/`, preserving the delivered measurements. The temporary compiled project is removed afterward.

Omitting `--output` writes to `validation/build_report.json` and replaces the corresponding delivered log and cross-check report. No project `.olean` cache is required or included in the archive.

## What is proved

The principal theorem is a strict comparison of two particular natural numbers at the contest input **42**. There are also independent and stronger structural certificates:

| Certificate | Meaning |
|---|---|
| `contender_5_lt_contender_6` | The final entry strictly exceeds the exact Lean port of Contender 5. |
| `contender_5_lt_contender_6_direct` | A second proof obtains the same comparison directly from the final reflector. |
| `preliminary_lt_contender_6` | The final entry strictly improves the completed preliminary construction. |
| `forty_three_arboreal_reflections_lt_contender_6` | It exceeds 43 successive arboreal reflections above the specified seed hierarchy, evaluated at 42. |
| `forty_one_forest_reflections_lt_contender_6` | It exceeds 41 successive forest reflections above the full forest contest-tree stage, evaluated at 42. |
| `finalFamily_not_representable` | No fixed expression in the specified final oracle language represents the entire final family. |

The final numerical definitions are short because the preceding modules define their components:

```lean
def finalOracles : Forest.Oracles
  | 0 => contenderFamily
  | k + 1 => ForestHierarchy.stage (Hierarchy.pad contestTree k)

def finalFamily (n : Nat) : Nat := Forest.reflect finalOracles n

def contender_6 : Nat := finalFamily 42
```

Forest reflection gives programs access to the entire function `Nat → Nat → Nat`, including a dynamically computed oracle index. It enumerates all expressions within a finite depth budget, evaluates them using total interpreters, and adds a positive overhead to their maximum. At input `n`, the depth budget is `n + 3`. Exact enumeration theorems therefore give a bound on every expression that fits this budget and eventual strict domination of every fixed expression in that language.

This is a statement about a precisely specified object language. It does not provide a universal evaluator for all Lean programs, enumerate halting Turing machines, or claim an optimal contest entry. The tree schedule uses raw well-founded trees; no unproved identification with a named ordinal or a standard fast-growing hierarchy is needed. The comparison proofs also avoid assuming that reflection is monotone when its oracle functions change.

## Architecture and module guide

The eleven verified modules total 2,465 source lines in this snapshot.

| Module | Role |
|---|---|
| [Original.lean](lean/Original.lean) | Source-faithful original interpreter, paired casts, reversed lookup, finite enumerators, `maxBy`, Contender 5, and axiom-free list/maximum proofs. |
| [Trees.lean](lean/Trees.lean) | Strictly positive countably branching `BTree`, structural operations, the dependent finite-type schedule, and the closed `treeIndex`. |
| [Reflection.lean](lean/Reflection.lean) | Companion development of unary-oracle reflection for the original natural-number language. It is verified but is not a dependency of the final entry. |
| [Hierarchy.lean](lean/Hierarchy.lean) | Generic unary reflection stages, finite prefix maxima, successor padding, reflection iteration, and bounded-path growth. |
| [Arboreal.lean](lean/Arboreal.lean) | Total raw-term language over `Nat`, `BTree`, and all finite arrow types; full tree recursion into arbitrary result types; exact depth enumeration; unary reflector `Rw`. |
| [Forest.lean](lean/Forest.lean) | Accessible countable oracle families, dynamic index selection, exact enumeration, forest reflection, and its comparison with `Rw`. |
| [Preliminary.lean](lean/Preliminary.lean) | The completed unary candidate, its contest tree and family, and its certified reflection-height margins. |
| [ForestHierarchy.lean](lean/ForestHierarchy.lean) | Tree-indexed reflection that retains the individual child functions at limit stages. |
| [Contender.lean](lean/Contender.lean) | The final oracle family, `contender_6`, both Contender 5 comparisons, and the final structural margins. |
| [Smoke.lean](lean/Smoke.lean) | Small kernel-reduction tests for binding, malformed casts, higher-type tree recursion, and dynamic forest calls. |
| [Audit.lean](lean/Audit.lean) | Explicit axiom-dependency checks for all 288 listed declarations. |

Every stage of the construction has its own scope. `Arboreal.Term.old` preserves the **closed numerical evaluation** of an original term. In contrast, `Forest.Expr.base` preserves the full arboreal environment, so the forest language can combine its family oracle with variables and natural/tree recursors inside higher-type functions.

## Recorded verification results

The delivered [build report](validation/build_report.json) records a successful fresh-source build with Lean 4.19.0, commit `6caaee842e94`, on x86-64 Linux. The [complete log](validation/lean_build.log) contains the individual reports.

| Check | Recorded result |
|---|---:|
| Eight modules in the final entry's dependency graph, including their proofs | **2.962263 seconds**, summed module times |
| All eleven delivered modules, including smoke checks and the axiom audit | **4.247454 seconds**, wall-clock time |
| Explicit declaration axiom audit | **288 / 288 empty lists** |
| Separate elaborated dependency-graph inspection | **PASS**, 0.836290 seconds |
| Independent original-semantics comparison | **PASS**, 25,134 values, 0.510469 seconds |

The eight-module and eleven-module measurements are below the contest's 15-second definition target on this host; the checks also fit the one-minute proof target. These are observed timings, not hardware-independent promises. The dependency inspection and Python comparison are supplementary checks timed separately from the eleven-module build.

The final definition's inspected logical closure contains 502 declarations, including 169 package declarations. It contains neither the original named contender nor the intermediate named number. The dependency inspection reports no axioms, unsafe or partial declarations, package-level `noncomputable` declarations, or package implementation replacements in that closure. It records ordinary Lean-core representation optimizations and `Nat.modCore` tags separately; these are not package additions or proof-certification assumptions. See [DependencyAudit.lean](validation/DependencyAudit.lean) and the retained report for the exact inspection.

The axiom audit is transitive: an empty list rules out dependencies such as `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the audited declaration. It does not prove the soundness of Lean's kernel inside Lean; verification uses the ordinary trust in the checker and its foundational rules.

The independent regression model agrees with Lean on enumeration counts and every numerical result, in enumeration order:

| Depth | Types | Terms | Largest value |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |
| 1 | 1 | 2 | 0 |
| 2 | 2 | 10 | 1 |
| 3 | 5 | 146 | 2 |
| 4 | 26 | 24,976 | 3 |

The smoke proofs additionally exercise tree recursion into `Nat`, `Nat → Nat`, and `BTree`, with both successor and countably branching inputs. Forest tests cover computed indices beyond the explicit prefix maximum, variables under lambdas, and family calls within tree-recursion branches. None of these tests evaluates a large contender or reflector.

## Original-source provenance and the port boundary

The upstream snapshot is pinned to commit [`d56dce013e6264292533efdc5e1de71863c6fb86`](https://github.com/codyroux/name-the-biggest-number/tree/d56dce013e6264292533efdc5e1de71863c6fb86). The archive retains [Contender.v](upstream/Contender.v), [the original contest rules](upstream/README.md), [the upstream MIT license](upstream/LICENSE), and [file hashes and source URLs](upstream/PROVENANCE.json).

The Lean port preserves the original raw syntax, source enumeration order, reversed de Bruijn lookup, recursively defined error values, paired arrow casts, and strict `maxBy` updates. It does not silently substitute a maximum over well-typed closed terms. Malformed terms need not evaluate to zero: for example, applying the successor constant to itself evaluates to 1 under the source's error-cast convention, and this case is tested.

Lean certifies the subsequent comparisons against the translated definition. The correspondence between that definition and Coq is a constructor-by-constructor source audit supported by finite independent regression tests. **It is not a machine-checked Coq-to-Lean compiler-correctness theorem.** Preserve the upstream copyright and license notice when redistributing its source or derived portions.

## Rebuild the article

The PDF is already included. To rebuild it, install `latexmk`, a PDF-capable LaTeX distribution, and the packages listed in the article preamble. From the archive root:

```bash
bash scripts/build_article.sh
```

The script runs `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` inside `article/`. Without Bash, the equivalent commands are:

```text
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The output is `article/article.pdf`. The included `article/validation_summary.tex` records the delivered validation run. Running the Lean verifier writes a new JSON report and log; it does not automatically replace this typeset historical summary.

## Artifact layout

| Location | Contents |
|---|---|
| `README.md`, `lean-toolchain` | This guide and the pinned Lean version. |
| `lean/` | The eleven verified source modules listed above. |
| `article/` | `article.tex`, `validation_summary.tex`, and the compiled `article.pdf`. |
| `scripts/` | The fresh-source verifier and article build script. |
| `validation/` | Build and cross-check reports, the build log, axiom target list, inspection drivers, the independent Python model, and PDF layout validation. |
| `upstream/` | Pinned original source, contest README, provenance, and license. |
| `environment/README.md`, `environment/lean_launcher.c` | Runtime note and source of the application-path launcher used in the recording environment. |

The launcher is retained for transparency because the recording environment could not use the usual executable-path discovery mechanism. It changes application-path discovery, not the Lean kernel or elaborator; [the runtime note](environment/README.md) records the details. **A normal Lean 4.19.0 installation does not need this launcher**; use its actual compiler binary with the commands above. The archive does not include a replacement compiler or a precompiled project.
