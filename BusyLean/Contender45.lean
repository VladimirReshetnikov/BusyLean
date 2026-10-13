import BusyLean.Contender44
import BusyLean.Ordinal.UniversalLanguage

/-!
# Contender 45: universal reflection above tree-indexed relative collapse

```
contender_45 := F45 (F45 42)
F45 n        := hier family44 (universalTree45 (family44 n)) (family44 n)
```

Contender 44 closes metalanguages under relative collapse with tree-indexed
levels.  Its object languages are nevertheless strongly normalizing typed
calculi.  Contender 45 adds a qualitatively different closure mechanism: a
fuel-bounded *untyped* higher-order tree machine with dynamic closures,
quotation, `eval`, and `self`.

Every recursive interpreter call consumes fuel.  Arbitrary self-application
and self-evaluation therefore remain total and computable; the language closure
takes a countable supremum over all finite fuels rather than asking a halting
question.  At a successor stage of `universalBoostT`, the machine receives the
entire previous language-closure operator as its higher-order `lift` primitive.
It can construct a transformer at run time, pass that transformer to the
previous closure, quote code, and evaluate generated or self code.

The new tree retains Contender 44's level-collapsing tree as branch zero.  A
positive branch stacks the universal language to the height of that same tree,
using a base transformer that joins the two input-reading impredicative jumps,
the official meta-jump, and Contender 44's tree-indexed collapsing closure.  The
final natural is read by the established hierarchy along this enlarged tree.

No halting oracle, unbounded minimization over termination, or Busy-Beaver
function occurs anywhere in the definition.

**Do not evaluate `contender_45`.**
-/

namespace BusyLean

/-- Contender 44's construction as a function of its input:
`family44 42 = contender_44`. -/
def family44 (n : Nat) : Nat := F44 (F44 n)

/-- The universal machine's base transformer.  Its branches rerun both genuine
input-reading impredicative jumps with the stronger `family44` oracle, retain
the official meta-jump, and expose Contender 44's tree-indexed collapsing
closure as a dynamic operation on the current input tree. -/
def base45 (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then FLT2.jumpL family44 N t
    else if i = 1 then FT2.jumpF family44 N t
    else if i = 2 then metaJump N t
    else closeL N (metaJump N) t

/-- Contender 44's tree, joined with the fuel-bounded universal-reflection
language stacked to that tree's own height. -/
def universalTree45 (N : Nat) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then levelTree44 N
    else Ordinal.universalBoostT (levelTree44 N) (base45 N) (levelTree44 N)

/-- The hierarchy along the universal-reflection tree, based on Contender 44's
family. -/
def F45 (n : Nat) : Nat :=
  Ordinal.hier family44 (universalTree45 (family44 n)) (family44 n)

/-- **Contender 45.** Never evaluate it. -/
def contender_45 : Nat := F45 (F45 42)

end BusyLean
