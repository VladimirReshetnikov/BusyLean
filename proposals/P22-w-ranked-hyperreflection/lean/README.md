# Lean overlay

Copy the `BusyLean/` directory into the repository root, copy
`test/Contender20Audit.lean` into `test/`, and add these imports to
`BusyLean.lean`:

```lean
import BusyLean.TreeHyperReflection
import BusyLean.TreeHyperReflectionFacts
import BusyLean.Contender20
import BusyLean.Comparison20
```

Then run:

```bash
lake build BusyLean.Contender20
lake build BusyLean.Comparison20
lake env lean test/Contender20Audit.lean
```
