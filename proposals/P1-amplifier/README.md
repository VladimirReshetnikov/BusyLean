# A constructive Lean contender beyond Contender 5

This package proposes the closed natural number `BigNumber.contender_6`, proves
that it strictly exceeds Contender 5 in Cody Roux's contest, and supplies a much
stronger lower bound. The complete 24-page article is
`article/Lean_Big_Number.pdf`; all LaTeX sources and Lean artifacts are included.

## Main result

Let `C5` be the exact computational port of the upstream fifth contender.
Define the tower of twos and its feedback iteration by

```text
T(0) = 1
T(h+1) = 2^T(h)
Theta(s,0) = s
Theta(s,k+1) = T(Theta(s,k)+1)
```

The checked theorems establish

```text
C5 < contender_6
Theta(C5+1,C5+1) <= contender_6
65^(C5+1) * (C5+2) <= contender_6 + 1
```

Thus the tower function is iterated more times than the incumbent's value,
starting from an integer already larger than that incumbent. The candidate's
actual definition also uses well-founded trees, higher function spaces,
explicit closure constructors, and score-dependent feedback. The lower bounds
are proved independently of any ordinal calibration of those constructors.

The submitted definition is:

```lean
namespace BigNumber

def contender_6 : Nat := Amplifier.candidate base

end BigNumber
```

Every custom dependency is present. The computational dependency graph does not
contain `BigNumber.Baseline.contender_5`, `largestOfDepth`, or
`largestSTLCNatRecNatOfDepth`. It intentionally reuses the general raw-language
interpreter and numerical envelope, rather than the incumbent's closed value.

## Rules used

The Coq contest is adapted to Lean 4.19.0, preserving constructive definitions,
strict comparison, no axioms, the 15-second definition budget, and the 60-second
proof budget. Times include the cumulative cost of rebuilding all custom
helpers from source, while permitting the official standard library to be
precompiled. The recorded proof budget additionally includes the axiom and
forbidden-dependency audits. Neither large natural number is evaluated.

This is a proposed contest entry with proved comparison results. It is not a
proof that the entry is maximal over every accepted Lean program, and it does
not claim official acceptance by the upstream contest.

## Verification

Use **Lean 4.19.0**, commit
`6caaee842e9495688c1567e78c0e68dbb96942aa`. No Mathlib dependency is required.
With this toolchain's `lean` executable on `PATH`, run:

```sh
python3 scripts/validate.py --lean lean \
  --forbid-dependency BigNumber.Baseline.largestOfDepth \
  --forbid-dependency BigNumber.Baseline.largestSTLCNatRecNatOfDepth \
  --recheck
```

The validator uses Python's standard library. It stages only source files in a
fresh temporary directory, rebuilds all eight required custom modules, checks
the time budgets, rejects nonempty transitive axiom lists, and verifies that
the final entry does not refer to the forbidden incumbent constants. With
`--recheck`, it also submits 264 safe stored custom bodies directly to the C++
kernel under fresh names. See `scripts/REPRODUCTION.md` for the exact scope of
this additional check and the disclosed environment-specific launcher used for
the recorded run.

Measured on an AMD EPYC 9V74 host running Ubuntu 24.04.3, with one compiler thread:

| Phase | Wall time |
| --- | ---: |
| All custom definitions | 1.408 s |
| All custom proofs | 1.363 s |
| Proofs plus axiom/dependency audits | 2.520 s |
| Additional stored-body kernel check | 2.458 s |

All **32 audited declarations have empty axiom lists**. The required eight
modules contain **697 lines / 25,777 UTF-8 bytes**. Peak resident memory for the
main compilation phases was about **428.3 MiB**. The full check, including the
extra kernel pass, peaked at about **927.9 MiB**. These are recorded measurements,
not universal guarantees for other machines.

An ordinary project build is also available:

```sh
lake build
```

For independent small-input validation:

```sh
python3 scripts/reference_model.py
```

That reference model agrees with Lean on syntax depths zero through four,
including 24,976 raw terms at depth four, and on a higher-type natural-recursion
example. Optional Lean test modules are `BigNumber/BaselineSmoke.lean` and
`BigNumber/SemanticChecks.lean`. They are not imported by the submitted entry.
The latter uses a larger local reduction-depth limit for its concrete test,
without changing the limits of the contest definition or proof modules.

## Exact incumbent and trust boundary

The upstream source is pinned at:

<https://github.com/codyroux/name-the-biggest-number/tree/d56dce013e6264292533efdc5e1de71863c6fb86>

Contender 5 is the maximum score of the source's total raw-term interpreter at
syntax depth 42. The translation preserves malformed terms, reversed variable
indices, both lambda annotations, structural error casts, natural recursion,
and the strict winner-selection rule. The theorem
`BigNumber.Baseline.contender_5_eq_envelope` connects that exact selected-winner
port to the numerical maximum used in the new base.

The cross-language correspondence is a reviewed computational translation,
supported by independent tests. It is not a formal verified Coq-to-Lean
translation theorem. The article and independent review state that boundary
explicitly.

The Veblen-inspired constructors are fully specified syntax, not a claim of
proved standard ordinal values. A supplied counterexample shows that an
unrestricted identification with the ordinary Veblen hierarchy would be false.
The strict and quantitative numerical comparisons do not need that
identification.

## Article build

From the archive root:

```sh
cd article
latexmk -xelatex -interaction=nonstopmode -halt-on-error Lean_Big_Number.tex
```

The article uses standard TeX packages, Latin Modern fonts, and DejaVu Sans Mono
for Unicode code listings. Its computational amplifier, base, and final
comparison files are included directly from the supplied Lean sources. Keep
that relative directory structure when rebuilding it.

## Package contents

- `article/`: compiled PDF, main LaTeX file, complete mathematical fragment,
  and measured validation table.
- `BigNumber/`: all definitions, proofs, axiom listings, and optional small tests.
- `scripts/`: clean validator, independent semantic model, and reproduction notes.
- `validation/`: exact measured report, compiler/audit logs, generated audit
  programs, small-model results, and independent mathematical review.
- `upstream/`: byte-exact pinned Coq source, original rules, original MIT license,
  and provenance hashes.
- `manifest.json` and `SHA256SUMS`: integrity records for the packaged files.

Build products such as `.olean`, temporary test files, the downloaded compiler,
and obsolete intermediate candidates are intentionally absent. The package
contains no changes to the upstream GitHub repository.

## Licensing and attribution

Upstream code is distributed under its original MIT license, preserved at
`upstream/LICENSE`. The translation retains attribution to Cody Roux, Samuel
Gruetter, and the upstream contributors. New code and explanatory text in this
package are also supplied under the MIT terms in the root `LICENSE`.
