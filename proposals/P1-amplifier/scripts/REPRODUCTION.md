# Reproducing the Lean checks

Use Lean **4.19.0**, Git commit
`6caaee842e9495688c1567e78c0e68dbb96942aa`.
No Mathlib dependency is required. The official `Std` and `Lean` modules that
ship with this release are sufficient.

From the project directory, with this toolchain's `lean` on `PATH`, run:

```sh
python3 scripts/validate.py --recheck
```

Alternatively pass `--lean /absolute/path/to/lean`, or set `LEAN_BIN` to that
path. The script uses Python's standard library. It writes the report to
`validation/validation.json` and keeps the compiler's complete output in
`validation/validation_logs/`.

The validator copies every required custom `.lean` source into a fresh temporary
directory and builds local imports in dependency order. It does not copy custom
`.olean` files or inherit `LEAN_PATH`. The cumulative definition time includes
all helpers used to define the entry. Proof time includes all remaining custom
proof modules. The strict transitive axiom audit has a separately reported time;
the report also checks that proofs plus this audit fit the 60-second limit.
Compiler launches use one thread for an explicit resource profile. These are
wall-clock measurements on the recorded host, not universal timing guarantees.

The ordinary compiler calls use `lean -o`, so declarations are elaborated and
kernel checked and module files are produced. No C code or executable is built,
and the gigantic natural number is never evaluated. The optional `--recheck`
pass explicitly submits a renamed copy of every safe custom definition,
theorem, and opaque body to `Kernel.Environment.addDeclCore`, preserving the
original declared type and universe parameters. Generated unsafe and partial
execution helpers are excluded; the safe logical bodies used by theorems are
included. Private custom declarations are recognized by their original names.
That API calls the C++ kernel's
declaration checker. This is a second check of the actual stored bodies; merely
issuing `#check` for an imported declaration would not do that. Imported standard
library declarations and inductive metadata are retained from the first build.
This verification overhead is reported separately from the entry's definition
and proof budgets.

The separate invocation also passes `--trust=0`, but this flag alone is **not**
treated as imported-body verification. Although Lean 4.19.0's command-line help
describes the flag as typechecking imports, the source of `finalizeImport`
installs imported constants directly and stores the trust flag. The explicit
`addDeclCore` loop makes the extra check concrete and reviewable.

`scripts/audit_names.txt` specifies the declarations whose complete transitive
axiom dependencies must be empty. `#print axioms` output is saved alongside a
programmatic assertion using Lean's `collectAxioms` function. Unused axioms
present in an imported standard module do not count as dependencies of an
entry. The audit rejects `sorryAx`, `propext`, `Classical.choice`, and
`Quot.sound` whenever any audited definition or theorem depends on them.
Lean's built-in proof irrelevance is a conversion rule, and its theorem
`proof_irrel` is proved by `rfl`; it is not an additional axiom declaration.

The same audit traverses the actual constant references in the declaration types
and bodies reachable from `BigNumber.contender_6`, using the `visited` set of
Lean's `CollectAxioms.collect` routine. It rejects a transitive dependency on
`BigNumber.Baseline.contender_5`. This is a dependency check on elaborated Lean
expressions, rather than a search for text in source files. Generic shared
functions, such as the enumerator, interpreter, and `envelope`, are permitted.
Additional forbidden declarations can be specified with
`--forbid-dependency`; a component-only build can explicitly use
`--no-dependency-audit` when the final entry is absent.

## Application-path adapter used for the recorded run

The execution environment for the recorded run does not expose
`/proc/<numeric-pid>/exe`. Lean 4.19.0 queries that path during startup to find its
installation. The supplied small C launcher records its own `argv[0]` path
instead and supplies this already-known pathname at the application's path
query. It reads no protected process information. All other path operations
retain the ordinary kernel access checks.

This adapter does **not** edit or replace Lean's kernel, elaborator, runtime
library, standard library source, or standard `.olean` files. The compiler
libraries are the unmodified official release. The source of the adapter is
`lean_launcher.c`; `build_launcher.sh` builds an optional `lean-compat` executable
in a supplied toolchain. This extra executable is unnecessary on a normal
machine, and no binary is included in the research package.

The official Linux release archive used for the recorded run is:

https://github.com/leanprover/lean4/releases/download/v4.19.0/lean-4.19.0-linux.tar.zst

SHA-256:

```text
archive:
6fe3ce97a58f44e2b3567d455b994eacec5bfe9ae7774f2a573444480ba813fe
official bin/lean:
92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023
official lib/lean/libleanshared.so:
2ab605c74c78f9ba4431a7b5305a4b28a9071d8a826f223eb14fe5530f78e14d
```

## Source references for the trusted-base discussion

These are pinned official Lean sources, verified through the GitHub connector:

- Proof irrelevance: `src/Init/Core.lean`, lines 777–778.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/Init/Core.lean#L777-L778
- Propositional extensionality: `src/Init/Core.lean`, line 1496.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/Init/Core.lean#L1496
- Quotient soundness: `src/Init/Core.lean`, line 1686.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/Init/Core.lean#L1686
- Function extensionality uses quotient soundness: lines 2180–2188.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/Init/Core.lean#L2180-L2188
- Choice: `src/Init/Prelude.lean`, line 770.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/Init/Prelude.lean#L770
- Transitive axiom collection: `src/Lean/Util/CollectAxioms.lean`.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/Lean/Util/CollectAxioms.lean
- Unconditional startup path initialization: `src/util/shell.cpp`.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/util/shell.cpp
- Application path implementation: `src/runtime/io.cpp`.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/runtime/io.cpp
- Import construction and direct kernel API: `src/Lean/Environment.lean`.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/Lean/Environment.lean
- Actual definition/theorem body checking: `src/kernel/environment.cpp`.
  https://github.com/leanprover/lean4/blob/6caaee842e9495688c1567e78c0e68dbb96942aa/src/kernel/environment.cpp
