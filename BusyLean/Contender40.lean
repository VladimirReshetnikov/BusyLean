import BusyLean.Contender39
import BusyLean.SystemFT2.Trees
import BusyLean.Ordinal.TreeLanguage4

/-!
# Contender 40: the impredicative jump under first-class language closure

```
contender_40 := F40 (F40 42)
F40 n        := hier family39 (metaTree (family39 n)) (family39 n)
```

Two new ingredients:

* **A genuine impredicative jump** (`FT2.jumpF`). System FT2 programs read an
  input tree and recurse over it into any type, so `jumpF g N t` contains every
  tree System F builds *from* `t`. The jump of Contenders 36-37 did not depend
  on its input beyond a finite truncation.
* **First-class language closure** (P27, `Ordinal.TreeLanguage4`). In the
  metalanguage, System T over trees can call a closure operator
  `lift : (tree → tree) → tree → tree`. `metaBoostT a` stacks such
  metalanguages along a tree `a`, each one calling the previous closure.

The base transformer joins the FT2 jump, Contender 31's collapse applied to
it, and Contender 39's mixed primitive. The metalanguage hierarchy over it
runs to the height of Contender 39's tree and is applied to that tree. The
number is read off with the hierarchy `hier` of Contender 38, with base
Contender 39's family.

**Do not evaluate `contender_40`.**
-/

namespace BusyLean

/-- Contender 39's construction as a function of its input: `family39 42 = contender_39`. -/
def family39 (n : Nat) : Nat := F39 (F39 n)

/-- The base transformer: the FT2 jump, collapse over it, and the mixed primitive. -/
def base40 (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then FT2.jumpF family39 N t
    else if i = 1 then Ordinal.boost31 (FT2.jumpF family39 N t)
    else mixed N t

/-- Contender 39's tree, closed under metalanguages over `base40` stacked to its own height. -/
def metaTree (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then mixTree N
    else Ordinal.metaBoostT (mixTree N) (base40 N) (mixTree N)

/-- The hierarchy along the meta-closed tree, based on Contender 39's family. -/
def F40 (n : Nat) : Nat := Ordinal.hier family39 (metaTree (family39 n)) (family39 n)

/-- **Contender 40.** Never evaluate it. -/
def contender_40 : Nat := F40 (F40 42)

end BusyLean
