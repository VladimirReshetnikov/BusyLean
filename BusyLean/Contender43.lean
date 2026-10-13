import BusyLean.Contender42
import BusyLean.Ordinal.UniversalLanguage

/-!
# Contender 43: universal reflection above relative collapse

```
contender_43 := F43 (F43 42)
F43 n        := hier family42 (universalTree43 (family42 n)) (family42 n)
```

Contender 42 closes the meta-jump under Buchholz-style collapse relative to
that jump.  Its object languages, however, are strongly normalizing typed
calculi.  Contender 43 adds a qualitatively different closure mechanism: a
fuel-bounded *untyped* higher-order tree machine with dynamic closures,
quotation, `eval`, and `self`.

Every recursive call of the interpreter consumes fuel.  Thus arbitrary
self-application and self-evaluation remain total and computable; the language
closure takes a countable supremum over all finite fuels rather than asking a
halting question.  At a successor stage of `universalBoostT`, the machine
receives the entire previous language-closure operator as its higher-order
`lift` primitive.  It can construct a transformer at run time, pass that
transformer to the previous closure, quote code, and evaluate generated or
self code.

The new tree retains Contender 42's relative-collapse tree as branch zero.  A
positive branch stacks the universal language to the height of that same tree,
using a base transformer that joins the input-reading ladder jump, System F
jump, the official meta-jump, and relative collapse.  The final natural is
read by the established hierarchy along this enlarged tree.

No halting oracle, unbounded minimization over termination, or Busy-Beaver
function occurs anywhere in the definition.

**Do not evaluate `contender_43`.**
-/

namespace BusyLean

/-- Contender 42's construction as a function of its input:
`family42 42 = contender_42`. -/
def family42 (n : Nat) : Nat := F42 (F42 n)

/-- The universal machine's base transformer.  Its branches rerun both genuine
input-reading impredicative jumps with the stronger `family42` oracle, retain
Contender 42's meta-jump, and expose the relative collapse as an operation on
the machine's current input tree. -/
def base43 (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then FLT2.jumpL family42 N t
    else if i = 1 then FT2.jumpF family42 N t
    else if i = 2 then metaJump N t
    else Ordinal.relCollapse (metaJump N) N t

/-- Contender 42's relative-collapse tree, joined with the fuel-bounded
universal-reflection language stacked to that tree's own height. -/
def universalTree43 (N : Nat) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then collapseTree N
    else Ordinal.universalBoostT (collapseTree N) (base43 N) (collapseTree N)

/-- The hierarchy along the universal-reflection tree, based on Contender 42's
family. -/
def F43 (n : Nat) : Nat :=
  Ordinal.hier family42 (universalTree43 (family42 n)) (family42 n)

/-- **Contender 43.** Never evaluate it. -/
def contender_43 : Nat := F43 (F43 42)

end BusyLean
