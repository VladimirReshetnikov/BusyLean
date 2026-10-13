# The Reflection Tree Contender

A reproducible Lean 4 proposal for Cody Roux's constructive biggest-number contest,
with the proof assistant changed from Coq to Lean.

## Main result

The submitted closed natural number is

    Biggest.contender_6 := hierarchy finalStage 43

The archive proves, in Lean:

    Biggest.contender_5_lt_contender_6 :
      contender_5 < contender_6

and the stronger lower bound

    x_0 = contender_5
    x_(j+1) = 2^(x_j + 44)
    x_5 <= contender_6.

Contender 5 is the exact depth-42 raw-language maximum ported from the pinned
upstream source. The new number is defined through an oracle reflection
operator and an explicit hierarchy of well-founded trees. Its compiled
dependency closure does not contain contender_5, baseline, largestOfDepth,
or maxBy. General syntax, interpretation, and enumeration are reused.

Read article/reflection_tree_contender.pdf for the complete mathematical
definition, motivation, proofs, and carefully stated limits.
All article sources are in article/*.tex.

## Verified configuration

- Lean 4.19.0, official release, commit 6caaee842e94.
- Only Init is imported by the contest modules; no Mathlib is needed.
- Fresh checking of definition modules: 1.404626 seconds (limit: 15).
- Remaining proofs, small checks, and both audits: 2.741057 seconds (limit: 60).
- All 144 inventoried public declarations have empty axiom dependency lists.
- The actual compiled dependency closure of contender_6 contains 444 constants.
- All nine arrays of small executable examples match their expected values.
- Neither Contender 5 nor the submitted huge number was evaluated.
- Timing is specific to the recorded machine and load; the verifier reapplies
  the same limits on each reproduction.

The main evidence is verification/results.json, with readable build.log and
complete compiler.log. The result file includes source hashes and confirms
the sources did not change during the checking run.

## Reproduce the Lean verification

Install the ordinary complete Lean 4.19.0 release, plus Python 3. From the
extracted archive root, run:

    python3 verification/verify.py \
      --lean /path/to/lean-4.19.0/bin/lean \
      --source-dir lean \
      --output verification/reproduced-results.json

The lean-toolchain file pins the same release for Elan. If the correct lean
is already on PATH, --lean lean is sufficient. The script uses fresh
temporary project object files and builds dependencies in order.
A Lake build is not required.

The script additionally imports official Lean environment-inspection modules
for its external compiled-dependency audit. These are included in a normal
complete Lean installation and are not dependencies of the contest term.

The checking container needed a narrowly scoped own-executable lookup
compatibility helper because of a PID/procfs namespace mismatch. Its complete
source and explanation are in verification/runtime/. It does not modify the
compiler or logical checking and is unnecessary on ordinary installations.
No binary runtime or precompiled project objects are bundled.

## Rebuild the article

With XeLaTeX and latexmk installed, from article/ run:

    latexmk -xelatex -interaction=nonstopmode -halt-on-error \
      reflection_tree_contender.tex

The document uses Latin Modern and DejaVu fonts and standard TeX packages
listed in its preamble. The included verification_metrics.tex records
the packaged checking run; it is not automatically overwritten on reproduction.

## Archive map

- RULES.md: proposed Lean adaptation of the contest.
- lean/: complete definitions, proofs, examples, and Main.lean.
- article/: full LaTeX source and compiled PDF.
- verification/: fresh-checking program and recorded evidence.
- reference/: exact original source, provenance, correspondence audit, MIT license.
- SHA256SUMS: integrity hashes for all other packaged files.
- lean-toolchain: version pin.

To verify the original source snapshot separately:

    python3 reference/verify_reference.py

## Assurance boundaries

The reference is frozen at upstream commit
d56dce013e6264292533efdc5e1de71863c6fb86:
https://github.com/codyroux/name-the-biggest-number

The Coq-to-Lean correspondence is a constructor-by-constructor manual audit
of the executable equations, supported by exact source preservation and
small examples. It is not a machine-checked theorem translating between
the two kernels. All subsequent enumeration, comparison, diagonal, and
growth theorems are machine-checked inside Lean.

Stage is a raw well-founded tree type. No exact named ordinal calibration,
growth-rate equivalence, or globally largest possible contest entry is claimed.
The proved fivefold exponential expression is a lower bound, not an estimate.
The fixed-program diagonal theorem is for the explicitly defined oracle
language, not for all Lean programs.

The original source and derivative portions retain the upstream MIT notice
provided in reference/LICENSE. The upstream repository files are reference
material; the Lean verification does not execute or depend on Coq.

Prepared 13 October 2026.
