# Source provenance

The proposal targets the following repository state:

- repository: `VladimirReshetnikov/BusyLean`
- branch: `main`
- commit: `1ee50c7d97bbed57a60709f661453c3e213f4db3`
- commit title: `Document Contender 13 in the README and the article`
- toolchain: `leanprover/lean4:v4.34.0`

The design reuses these baseline components:

- `BusyLean/Contender13.lean`: `Fd.fvalue`, `Fd.reflectFd`, `F13`, and
  `contender_13`;
- `BusyLean/Comparison13.lean`: the direct dynamic-reflection inequalities and
  `contender_12_lt_contender_13`;
- `BusyLean/MetaReflection.lean`: `Transformer`, `liftTransformer`, and
  `operatorStage`;
- `BusyLean/MetaReflectionFacts.lean`: `Progressive`,
  `operatorStage_progressive`, `transformer_lt_lift_at`, and
  `operatorStage_child_lt`;
- `BusyLean/Contender12.lean` and `BusyLean/Autonomous.lean`: `tree12`, encoded
  autonomous syntax, realization, and the `hyper` hierarchy;
- `BusyLean/Contender9.lean`: `packFamily`;
- `README.md`, `test/Audit.lean`, and `scripts/check.py`: contest rules and
  validation conventions.

No repository files were modified remotely. The deliverable is an overlay and
unified patch for review and local kernel checking.
