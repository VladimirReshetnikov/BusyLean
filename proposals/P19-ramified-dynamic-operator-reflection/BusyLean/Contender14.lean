import BusyLean.Contender13
import BusyLean.MetaReflection
import BusyLean.Autonomous

/-!
# Contender 14: ramified dynamic operator reflection

Contender 13 performs one reflection step over dynamic-kind System Fω with a
unary oracle.  This file makes four construction-level upgrades, without ever
mentioning the constant `contender_13` in the new number's dependency closure.

1. `reflectFdFamily` gives dynamic-kind System Fω a packed countable oracle
   family and dominates every visible coordinate of that family.
2. `fdFamilyTransformer` packages this as a progressive transformer.
3. `towerStep` feeds a transformer's output back into a full operator-stage
   closure along `tree14`, a schedule obtained by stacking another autonomous
   hyper-closure above Contender 12's `tree12`.
4. `operatorTower (n+1)` nests this strict meta-step an input-dependent number
   of times.  Its seed exposes every finite additional iterate of the
   Contender-13 construction.

```
family13 n       = F13 (F13 n)
iterateF13 i x   = F13^[i] x
seed13 i n       = iterateF13 i (family13 n)
operatorTower 0  = fdFamilyTransformer
operatorTower(k+1) = towerStep (operatorTower k)
F14 n            = operatorTower (n+1) seed13 n n
contender_14      = F14 (F14 42)
```

All recursion is structural.  There is no use of `noncomputable`, `partial`,
`unsafe`, `opaque`, `implemented_by`, `extern`, or an unbounded search.

**Do not evaluate `contender_14`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Reflection over dynamic-kind System Fω with a packed countable oracle
family.  Besides all accepted program values, it strictly exceeds each
coordinate `fs i n` visible at the current budget (`i ≤ n`). -/
def reflectFdFamily (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN
    (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fd.fvalue (packFamily fs) n) (Fd.ctmsUpTo n))

/-- One family-aware dynamic-kind reflection step, as a transformer.  The
output-family coordinate is intentionally ignored. -/
def fdFamilyTransformer : Transformer :=
  fun fs _ n => reflectFdFamily fs n

/-- A second autonomous schedule above Contender 12's schedule.  Recall that
`tree12 = realize (hyper 42 (encode index))`; here the same closure is stacked
once more above `tree12`. -/
def tree14 : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper 42 (Autonomous.encode tree12))

/-- One strict meta-step.  First run `base` on `seed`; then use that whole
output family as the seed of a full operator-stage closure of `base`.

When `base` is progressive, `towerStep base` is progressive and strictly
exceeds `base` pointwise on every visible coordinate; these facts are proved
in `Comparison14.lean`. -/
def towerStep (base : Transformer) : Transformer :=
  fun seed => (operatorStage base tree14) (base seed)

/-- The ramified operator tower.  Level zero is family-aware dynamic-kind
reflection.  Every successor level applies a full `towerStep` to the preceding
level. -/
def operatorTower : Nat → Transformer
  | 0 => fdFamilyTransformer
  | k + 1 => towerStep (operatorTower k)

/-- Contender 13's construction as a function of its input:
`family13 42 = contender_13`.  The constant `contender_13` itself is not used. -/
def family13 (n : Nat) : Nat := F13 (F13 n)

/-- Right-associated finite iteration of the Contender-13 reflector. -/
def iterateF13 : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => F13 (iterateF13 k n)

/-- The seed family exposes arbitrarily many additional `F13` iterations to
packed-oracle programs and to the transformer machinery.  Coordinate zero is
exactly `family13`; coordinate `i` adds `i` further reflection steps. -/
def seed13 : W.Family :=
  fun i n => iterateF13 i (family13 n)

/-- The Contender-14 family.  At input `n` it uses `n+1` nested operator-tower
levels, reads coordinate `n`, and evaluates at numerical input `n`. -/
def F14 (n : Nat) : Nat :=
  operatorTower (n + 1) seed13 n n

/-- **Contender 14.** Never evaluate it. -/
def contender_14 : Nat := F14 (F14 42)

end BusyLean
