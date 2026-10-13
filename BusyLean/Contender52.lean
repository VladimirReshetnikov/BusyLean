import BusyLean.Ordinal.UniverseLanguage
import BusyLean.Contender51

/-!
# Contender 52: first-class universe-program reflection

```
contender_52 := F52 (F52 42)
F52 n        := hier (ladderReflect family51 T) T N
                where N = family51 n, T = universeTree52 N
```

Contender 51 makes tree iteration operators first-class primitives of a
System-T language. Its programs still manipulate naturals, trees, and tree
operators; the universe records consumed by relativized collapse remain fixed
meta-level Lean objects.

`Ordinal.UL` adds a distinct semantic kind, `univ`, interpreted by `U2.Univ`.
Object-language programs may build universes, abstract over universe operators,
close transformers at operator kind, index universes by their input tree, and
collapse a program-built universe relative to a program-visible closure
operator. `universeLanguageLift` joins a canonical operator-closure witness
with every bounded closed tree-valued program of this language.

Here the input tree is Contender 51's full primitive-program tree and the
visible closure operator is `closeU N (metaJump N)`. The resulting tree is read
with the accepted ladder reflection, so the new ingredient is a semantic kind
change rather than another iteration operator or another numeric reader.

**Do not evaluate `contender_52`.**
-/

namespace BusyLean

/-- Contender 51's construction as a function of its input. -/
def family51 (n : Nat) : Nat := F51 (F51 n)

/-- Contender 51's whole program tree, closed under bounded programs whose
first-class values include universes and universe operators. -/
def universeTree52 (N : Nat) : Ordinal.CTree :=
  Ordinal.universeLanguageLift (closeU N (metaJump N)) (primTree N) N

/-- Read the universe-program-closed tree with ladder reflection, then run the
repository hierarchy along that same tree. -/
def F52 (n : Nat) : Nat :=
  let N := family51 n
  let T := universeTree52 N
  Ordinal.hier (ladderReflect family51 T) T N

/-- **Contender 52.** Never evaluate it. -/
def contender_52 : Nat := F52 (F52 42)

end BusyLean
