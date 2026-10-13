import BusyLean.Ordinal.UniverseLanguage
import BusyLean.Contender48

/-!
# Contender 49: first-class universe-program reflection

```
contender_49 := F49 (F49 42)
F49 n        := hier family48 (universeTree49 (family48 n)) (family48 n)
```

Contenders 40--48 remain, at object-language level, in the kind
`tree → tree`: their programs manipulate trees and tree operators.  Universe
builders (`U2.Univ`, `next`, `union`, closure functionals and relativized
collapse) are fixed meta-level primitives.

`Ordinal.UL` adds a total typed language with a new base kind `univ`.
Programs can construct universes, abstract over universe operators, take
closure points at universe and operator kind, and collapse a program-built
universe relative to a program-built tree operator.  The bounded collection of
all such programs is joined by `universeLanguageLift`.

Thus the new ingredient is a kind change, not another iterate of the existing
iteration hierarchy.

**Do not evaluate `contender_49`.**
-/

namespace BusyLean

/-- Contender 48's construction as a function of its input. -/
def family48 (n : Nat) : Nat := F48 (F48 n)

/-- The old universe-collapsing closure together with the new first-class
universe-program jump. -/
def close49 (N : Nat) (J : Ordinal.CTree → Ordinal.CTree)
    (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then closeU N J t
    else Ordinal.universeLanguageLift J t N

/-- Put the new closure under the existing first-class metalanguage, using the
strongest Contender 48 iteration operator as its base. -/
def universeTree49 (N : Nat) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then levelIterTree N
    else Ordinal.metaBoostC (close49 N) (levelIterTree N)
      (iterLevel N (levelIterTree N) (metaJump N) (levelIterTree N))
      (levelIterTree N)

/-- The hierarchy along the universe-program-closed tree. -/
def F49 (n : Nat) : Nat :=
  Ordinal.hier family48 (universeTree49 (family48 n)) (family48 n)

/-- **Contender 49.** Never evaluate it. -/
def contender_49 : Nat := F49 (F49 42)

end BusyLean
