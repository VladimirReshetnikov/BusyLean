import BusyLean.Contender41
import BusyLean.Ordinal.UniversalLanguage

/-!
# Contender 42: fuel-bounded universal reflection

```
contender_42 := F42 (F42 42)
F42 n        := hier family41 (universalTree (family41 n)) (family41 n)
```

Contender 41 still closes its trees under strongly normalizing typed object
languages.  Contender 42 introduces a different mechanism: an untyped
higher-order tree machine with explicit fuel, dynamic closures, quotation,
`eval`, and `self`.  Every interpreter call consumes fuel, so every branch is
total and computable even when a program self-applies or evaluates itself.
The language closure ranges over every finite fuel, syntax depth, and program.

At a successor of `universalBoostT`, programs receive the entire previous
whole-language closure as the `lift` primitive.  They may create closures at
run time, pass them through `lift`, quote code, and evaluate generated or
self code.  This is intensional universal reflection, not another numerical
parameter increase or another externally stacked typed language.

The baseline branch retains Contender 41's reader tree.  The final natural is
read by the established hierarchy along the new universal-reflection tree.

**Do not evaluate `contender_42`.**
-/

namespace BusyLean

/-- Contender 41's construction as a function of its input:
`family41 42 = contender_41`. -/
def family41 (n : Nat) : Nat := F41 (F41 n)

/-- The base tree transformer at level 42.  The first two branches rerun the
input-reading ladder and impredicative jumps with the stronger `family41`
oracle; the third retains all of Contender 41's base transformer. -/
def base42 (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then FLT2.jumpL family41 N t
    else if i = 1 then FT2.jumpF family41 N t
    else base41 N t

/-- Contender 41's tree, joined with the universal reflective language stacked
to that tree's own height. -/
def universalTree (N : Nat) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then readerTree N
    else Ordinal.universalBoostT (readerTree N) (base42 N) (readerTree N)

/-- The hierarchy along the universal-reflection tree, based on Contender 41's
family. -/
def F42 (n : Nat) : Nat :=
  Ordinal.hier family41 (universalTree (family41 n)) (family41 n)

/-- **Contender 42.** Never evaluate it. -/
def contender_42 : Nat := F42 (F42 42)

end BusyLean
