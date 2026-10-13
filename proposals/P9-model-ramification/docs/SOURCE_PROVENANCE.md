# Source provenance

Repository: `VladimirReshetnikov/BusyLean`  
Pinned revision: `86b360648163f0249eab79539438b6a83dfe8215`  
Retrieval date: October 12, 2026 (America/Los_Angeles)

The GitHub connector was used to inspect the root README, current contender,
reflection definitions and facts, comparison theorems, proposal review, P5
language definitions and proofs, and audit code. The article bibliography
links to the exact pinned paths. The three vendored definition files match
the original Git blob hashes, not merely their displayed names.

| Local file | Original repository path |
|---|---|
| `lean/BigNumber/Definitions.lean` | `proposals/P5-w-reflection/lean/BigNumber/Definitions.lean` |
| `lean/BusyLean/Reflection.lean` | `BusyLean/Reflection.lean` |
| `lean/BusyLean/Contender6.lean` | `BusyLean/Contender6.lean` |

`evidence/vendor_hashes.json` and `evidence/source_audit.json` record exact
expected and computed Git blob hashes. The standalone build intentionally
vendors definitions only; the original comparison modules are not required
for the direct C6/C7 comparison. The optional transitive corollaries require
the full pinned repository.

New material is under `lean/BusyLean7/`, `python/`, `scripts/`, and `article/`.
The transitive closure traversal in `test/Audit.lean` is adapted from the
pinned repository's audit. The root `LICENSE` preserves the repository's
MIT-0 license; `docs/UPSTREAM_MIT_LICENSE.txt` preserves the original Coq
project's MIT notice.

No source file or compiled artifact in the user's GitHub repository was
modified. No downloaded toolchain binaries or font files are redistributed.
