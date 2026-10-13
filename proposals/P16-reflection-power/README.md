# BusyLean Contender 7 research package

This package proposes **Contender 7: seeded reflection power** for
`VladimirReshetnikov/BusyLean`.

The defining equation is:

```lean
def contender_7 : Nat := stageOrder metaHeight p5Family index 42
```

with

```lean
def metaHeight : Nat := Nat.succ (42 + p5Family 0 42)
```

and `stageOrder` obtained by repeatedly reflecting the *entire preceding
scheduler* through the universal W-tree index.  The supplied comparison proof
establishes the intended chain

```text
Contender 5 < P5/Contender 6 predecessors < BusyLean Contender 6 < Contender 7.
```

See `article/reflection_power_contender.pdf` for the mathematical development,
`BUILD.md` for integration, and `VALIDATION.md` for the exact verification
status.
