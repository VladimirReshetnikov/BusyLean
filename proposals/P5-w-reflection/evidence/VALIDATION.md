# Observed validation boundary

## Executed

- The Python standard-library test suite completed all six groups without
  failures or errors. See `python_tests.json` and `python_tests.log`.
- Enumeration and numerical scores were tested exhaustively through depth four,
  not depth 42. Additional tests checked the specified semantic edge cases.
- The lexical Lean source audit passed. See `source_audit.json`. This does not
  establish elaboration success, termination-checker acceptance, or absence of
  axioms in elaborated dependencies.
- pdfLaTeX produced the article, with resolved references and no final-pass
  overfull-box warnings. Its pages were rendered and visually inspected.

## Not executed

The pinned Lean compiler was not installed in the producing runtime. The
checker records `status: not_run`, `kernel_checked: false`, and
`timing_verified: false`. No formal-kernel success or timing certificate has
been inferred from the Python tests or source shape.

The proposed Lean proof concerns the strict comparison to the numerical port
of Contender 5. The exact source-port correspondence, universal-envelope theorem,
W-language conservative inclusion, and tower-height lower bound are supplied as
paper proofs, not separately machine-checked theorems.

The main number was not evaluated. No decimal value or numerical approximation
is claimed. A successful native compile, actual empty-axiom output, and both
checking-time gates remain necessary before claiming contest compliance.
