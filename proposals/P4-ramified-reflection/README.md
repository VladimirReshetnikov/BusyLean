# A constructive Lean contender beyond Contender 5

**Research proposal, 12 October 2026. Prepared for Vladimir Reshetnikov.**

## Status first

The article supplies a constructive mathematical definition and complete
mathematical comparison proofs. The package includes proposed Lean definition
and proof source, with no proof placeholders found by its source screen.
**The Lean source has NOT been compiler-checked.** No Lean toolchain was
available in the preparation environment, and download attempts failed.
The empty-axiom audit and the 15-second / 60-second timing gates are therefore
**unverified**. This is not an already accepted contest entry.

The Python small-instance model passed **62,065 assertions**. These tests do
not replace Lean kernel checking. The stronger tower and diagonal-escape
results are proved in the article, but are not formalized as Lean theorems
in this package.

## The proposed number

The declaration is `BigNumber.contender_6 := reflect grandIndex 64`.
In the article's notation it is **N = R_Theta(64)**.

- `M_q(d)` is the finite maximum of numerical outputs of raw programs of
  weighted depth at most `d` in a total language. This language has natural
  recursion, a strictly positive well-founded-tree type and its recursor at
  every finite result type, a binary oracle parameter, and explicitly
  depth-charged quotation of any raw legacy term interpreted in the empty
  environment.
- `R_zero(n) = M_0(n+4)` and
  `R_sup(f)(n) = M_((i,x) -> R_(f(i))(x))(n+4)` are defined by tree recursion.
- `H_k(a;s)` diagonalizes countable iteration through the finite-type tower
  `L_0 = Tree`, `L_(k+1) = L_k -> L_k`.
- `Boost(a)` has child 0 equal to `a`, and child `k+1` equal to
  `H_(R_a(k+64))(a;Step)`, where `Step(a)=sup(_ -> a)`.
- `Theta = sup(k -> H_k(zero;Boost))`.

All details, depth conventions, interpreters, and recursors are specified in
`article/article.tex`, `article/article.pdf`, and the source files.

## Main mathematical results

For the exact upstream Contender 5, denoted C5:

    C5 < N
    E_(C5+1)(64) < N

Here `E_0(x)=x` and `E_(j+1)(x)=2^(E_j(x))`. Thus the proposal exceeds a
base-2 exponential tower with C5+1 exponentiation steps above the seed 64.
C5 appears only in the comparisons, not in the entry's definition.

Other proved results include visible-child separation, an explicit
2^28-branch visibility bound at input 64, oracle-fed iteration, and eventual
domination of every fixed unary program in a stage's own object language.
There is no claim of absolute optimality or of a sharp named ordinal rank.

The exact Coq baseline preserves raw malformed-term semantics, including
computational defaults, casts, and absolute binder levels. Replacing it with
a typechecking/rejection evaluator would change the target. The paper gives
a semantic port argument; it is not a cross-kernel translation certificate.

## Contents

| Path | Purpose |
|---|---|
| `article/article.tex`, `article/article.pdf` | Full research article and compiled PDF |
| `lean/BigNumber/*.lean` | Definitions, baseline, proposed comparison proofs, audit, smoke tests |
| `lean/lean-toolchain` | Pinned target: `leanprover/lean4:v4.35.0` |
| `python/model.py`, `python/test_model.py` | Executable small-instance model and tests |
| `scripts/verify_lean.py` | Cold package build, strict axiom checks, timing gates |
| `scripts/build_article.sh` | Rebuild PDF using latexmk |
| `validation/` | Actual test results, Lean-unavailable status, PDF build/inspection information |
| `provenance/` | Upstream commit/blob references and MIT notice |
| `RESEARCH_STATUS.md` | Theorem and validation boundaries |
| `MANIFEST.sha256` | Checksums of delivered files except the manifest itself |

The definition dependency closure is
`ListKit -> Legacy -> Language -> Hierarchy -> Contender`.
`Baseline` is imported only downstream for the comparison proof. No previous
winning numerical constant is imported by the entry module.

## Reproduce

Use Python 3.10 or newer for the model and acceptance utility; the recorded
model run used the preparation environment's Python 3.13. No third-party
Python packages are required for these two scripts.

```sh
python python/test_model.py
bash scripts/build_article.sh
```

The document requires a TeX distribution with latexmk, pdfLaTeX, AMS packages,
Latin Modern, stmaryrd, xurl, microtype, listings, and the other ordinary
packages listed in its preamble. It does not need external bibliography data.

On a machine with the pinned Lean toolchain installed and `lean` on PATH:

```sh
python scripts/verify_lean.py
```

`LEAN=/absolute/path/to/lean` may select a compiler executable. The utility
checks its version, removes only generated Lean module artifacts inside this
package, builds every new definition module under an aggregate 15-second
budget, and then the proof/audit/smoke modules under an aggregate 60-second
budget. It requires empty transitive axiom reports for the specified entry
and proofs. Any compiler failure or gate failure prevents acceptance.
A missing compiler produces exit status 2, as it did during preparation.

Standard-library distribution artifacts are allowed to be prebuilt. No
contestant-created precompiled definition is hidden outside the timed
module list. The utility is an ordinary audit aid, not a security-certified
sandbox. A judge should disclose hardware, inspect the compiler provenance,
and review the recorded logs.

**Do not run `#eval contender_6` or request a decimal expansion.** The aim is
checking a total definition and a proof, not evaluating the number.

## Provenance

Upstream: `codyroux/name-the-biggest-number`.

- Commit: `d56dce013e6264292533efdc5e1de71863c6fb86`
- `Contender.v` blob: `f92db72deb0f3a4d4e3b575b4949eda73b1417a0`
- Contender 5 attribution in the source: `samuelgruetter`

The legacy computational port derives from MIT-licensed upstream material;
the complete required notice is included in `provenance/UPSTREAM_LICENSE.txt`.
The upstream repository itself was not mirrored or compiled. No toolchain
binary or font file is included.
