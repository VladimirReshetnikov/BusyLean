import BusyLean.Ordinal.UniverseLanguage
import BusyLean.Contender50

/-!
# Contender 51: first-class universe-program reflection

```
contender_51 := F51 (F51 42)
F51 n        := hier (ladderReflect family50 T) T N
                where N = family50 n, T = universeTree51 N
```

Contender 50 reads its frontier tree with both System FT2 and ladder-language
programs, but those object languages still manipulate numbers, trees, and tree
operators. Universe builders (`U2.Univ`, `next`, `union`, closure functionals,
and relativized collapse) remain fixed meta-level Lean primitives.

`Ordinal.UL` adds a total typed language with a new base kind `univ`.
Programs can construct universes, abstract over universe operators, take
closure points at universe and operator kind, and collapse a program-built
universe relative to a program-built tree operator. The bounded collection of
all such programs is joined by `universeLanguageLift`.

The resulting tree is then read with Contender 50's strongest accepted reader,
so the new ingredient is a semantic kind change rather than another iteration
level or a weaker replacement for the current frontier.

**Do not evaluate `contender_51`.**
-/

namespace BusyLean

/-- Contender 50's construction as a function of its input. -/
def family50 (n : Nat) : Nat := F50 (F50 n)

/-- The old universe-collapsing closure together with the new first-class
universe-program jump. -/
def close51 (N : Nat) (J : Ordinal.CTree → Ordinal.CTree)
    (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then closeU N J t
    else Ordinal.universeLanguageLift J t N

/-- Put the new closure under the existing first-class metalanguage, using the
strongest Contender 48 iteration operator as its base. -/
def universeTree51 (N : Nat) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then levelIterTree N
    else Ordinal.metaBoostC (close51 N) (levelIterTree N)
      (iterLevel N (levelIterTree N) (metaJump N) (levelIterTree N))
      (levelIterTree N)

/-- Read the new universe-program-closed tree with Contender 50's ladder
reflection, then run the repository hierarchy along that same tree. -/
def F51 (n : Nat) : Nat :=
  let N := family50 n
  let T := universeTree51 N
  Ordinal.hier (ladderReflect family50 T) T N

/-- **Contender 51.** Never evaluate it. -/
def contender_51 : Nat := F51 (F51 42)

end BusyLean
