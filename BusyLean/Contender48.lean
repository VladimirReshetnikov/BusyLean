import BusyLean.Contender47
import BusyLean.Ordinal.UniversalLanguage

/-!
# Contender 48: fuel-bounded universal reflection above iterated self-basing

```
contender_48 := F48 (F48 42)
F48 n        := hier family47 (universalTree48 (family47 n)) (family47 n)
```

Contender 47 iterates the self-based construction itself along a tree, but its
object languages remain strongly normalizing typed calculi. Contender 48 adds a
qualitatively different closure mechanism: an untyped higher-order tree machine
with dynamic closures, quotation, `eval`, lexical `self`, and a first-class
`lift` primitive for the entire preceding language closure.

Every interpreter call consumes explicit fuel. Arbitrary self-application and
self-evaluation are therefore total; the whole-language tree ranges over every
finite fuel rather than deciding whether a program halts. At successor stages
of `universalBoostT`, a machine can construct a transformer at run time and
pass it to the whole preceding closure.

The new tree retains Contender 47's `psiTree` as branch zero. A positive branch
stacks the universal language to the height of that tree. Its base transformer
exposes the two input-reading impredicative jumps, a fresh iteration of `psi`
along the complete Contender 47 tree, and the universe-collapsing closure
relative to that stronger operator.

No halting oracle, Busy-Beaver function, or unbounded minimization over
termination occurs in the definition.

**Do not evaluate `contender_48`.**
-/

namespace BusyLean

/-- Contender 47's construction as a function of its input:
`family47 42 = contender_47`. -/
def family47 (n : Nat) : Nat := F47 (F47 n)

/-- The strongest accepted iteration, used as a semantic primitive by the
universal machine. -/
def psi47 (N : Nat) : Ordinal.CTree → Ordinal.CTree :=
  psi N (psiTree N)

/-- Dynamic base transformer for the universal language. -/
def base48 (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then FLT2.jumpL family47 N t
    else if i = 1 then FT2.jumpF family47 N t
    else if i = 2 then psi47 N t
    else closeU N (psi47 N) t

/-- Contender 47's tree joined with the universal-reflection stack to that
same tree's height. -/
def universalTree48 (N : Nat) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then psiTree N
    else Ordinal.universalBoostT (psiTree N) (base48 N) (psiTree N)

/-- The hierarchy along the universal-reflection tree, based on Contender 47's
family. -/
def F48 (n : Nat) : Nat :=
  Ordinal.hier family47 (universalTree48 (family47 n)) (family47 n)

/-- **Contender 48.** Never evaluate it. -/
def contender_48 : Nat := F48 (F48 42)

end BusyLean
