# Provenance and licensing

The three files listed in `evidence/SOURCE_MANIFEST.json` are exact copies from
VladimirReshetnikov/BusyLean, commit
`86b360648163f0249eab79539438b6a83dfe8215`. Their Git blob hashes were checked.
They inherit BusyLean's MIT-0 license. The earlier Coq contest and its porting
lineage are credited to codyroux, samuelgruetter, and the upstream contributors;
the original MIT notice is retained in `licenses/Original-Contest-MIT.txt`.

The new semantic-mirror construction, explanatory article, Lean source, Python
reference model, and scripts were prepared for Vladimir Reshetnikov. They may be
used under the MIT-0 terms in `LICENSE`. `Mirror/Audit.lean` adapts the pinned
repository's dependency-closure traversal. No claim of established priority or
independent publication is made.

The Lean files added by this package have NOT been compiled in the generating
environment. See `VALIDATION.md`. Included upstream comments describing older
verification results refer to upstream work, not verification of this package.
