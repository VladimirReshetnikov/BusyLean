import BusyLean.Contender50
import BusyLean.Ordinal.UniversalLanguage

/-!
# Contender 51: universal reflection with ladder readout

```
contender_51 := F51 (F51 42)
F51 n        := hier (reader51 N) (universalTree51 N) N
                where N = family50 n
```

Contender 50 reads the final iteration-level tree with strongly normalizing
ladder programs. Contender 51 first enlarges that tree by a qualitatively
different mechanism: a fuel-bounded *untyped* higher-order tree machine with
dynamic closures, unrestricted self-application, quotation, `eval`, lexical
`self`, and first-class access to the entire preceding language closure.
It then applies Contender 50's strongest ladder reader to the enlarged tree.

Every recursive call of the interpreter consumes explicit fuel. Arbitrary
self-application and self-evaluation therefore remain total and computable; the
whole-language tree ranges over every finite fuel rather than deciding whether
a program halts. At successor stages of `universalBoostT`, a machine may build
a transformer at run time and pass it to the complete preceding closure.

Branch zero of `universalTree51` retains Contender 48's official
`levelIterTree`, which is also the tree read by Contenders 49 and 50. Every
positive branch stacks the universal language to that tree's height. The
machine base exposes the two input-reading impredicative jumps, one more run of
the accepted iteration-level hierarchy, and universe collapse relative to that
operator. Finally `reader51` uses Contender 50's ladder reflection over the new
universal tree.

No halting oracle, Busy-Beaver function, or unbounded minimization over
termination occurs in the definition.

**Do not evaluate `contender_51`.**
-/

namespace BusyLean

/-- Contender 50's construction as a function of its input:
`family50 42 = contender_50`. -/
def family50 (n : Nat) : Nat := F50 (F50 n)

/-- Run the accepted tree-indexed hierarchy of iteration levels once more along
its complete official tree, exposing the resulting operation to UTL programs. -/
def iterLevel50 (N : Nat) : Ordinal.CTree → Ordinal.CTree :=
  iterLevel N (levelIterTree N) (metaJump N) (levelIterTree N)

/-- Dynamic base transformer for the universal language. -/
def base51 (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then FLT2.jumpL family50 N t
    else if i = 1 then FT2.jumpF family50 N t
    else if i = 2 then iterLevel50 N t
    else closeU N (iterLevel50 N) t

/-- The official final tree joined with the fuel-bounded universal-reflection
stack to that same tree's height. -/
def universalTree51 (N : Nat) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then levelIterTree N
    else Ordinal.universalBoostT (levelIterTree N) (base51 N) (levelIterTree N)

/-- Contender 50's strongest numeric reader, now applied to the enlarged
universal-reflection tree and using the stronger predecessor family. -/
def reader51 (N : Nat) : Nat → Nat :=
  ladderReflect family50 (universalTree51 N)

/-- The hierarchy along the universal-reflection tree, based on its own ladder
reader. -/
def F51 (n : Nat) : Nat :=
  Ordinal.hier (reader51 (family50 n))
    (universalTree51 (family50 n)) (family50 n)

/-- **Contender 51.** Never evaluate it. -/
def contender_51 : Nat := F51 (F51 42)

end BusyLean
