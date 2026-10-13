import BusyLean.Contender64

/-!
# Contender 65: a hierarchy of step operators

```
contender_65 := F65 (F65 42)
F65 n        := hier ((towerFrom (metaS N family64 T) (base61 N family64) T).2 family64) T N
```

Contenders 57-64 follow one pattern. A *step* `S : Closures → Closures`
produces the next closure pair. `towerFrom S c` iterates it along a tree from
`c`. The tower then becomes a value of a new language, which gives a new step.
Contender 65 makes the pattern itself a hierarchy:

* `metaStep S c` closes Contender 61's language plus `towerFrom S c` as a
  height-indexed family of closures;
* `metaS 0 = step2` (Contender 64's step), `metaS (a+1) = metaStep (metaS a)`,
  and limits are pointwise.

So `metaS a` is the pattern applied `a` times, for a transfinite tree `a`. The
meta-level, the tower height and the argument are Contender 64's tree, then the
tree this builds.

**Do not evaluate `contender_65`.**
-/

namespace BusyLean

open Ordinal (CTree Closures)

/-- Iterate a step along a tree from `c0`, pointwise at limits. -/
def towerFrom (S : Closures → Closures) (c0 : Closures) : CTree → Closures
  | .zero => c0
  | .succ a => S (towerFrom S c0 a)
  | .lim f =>
      (fun b t => .lim fun i => (towerFrom S c0 (f i)).1 b t,
       fun g m => Ordinal.maxUpTo (fun i => (towerFrom S c0 (f i)).2 g m) m)
  | .supL _ => c0
  | .supH _ => c0

/-- The closures of Contender 61's language. -/
def base61 (N : Nat) (g : Nat → Nat) : Closures :=
  (Ordinal.ptl2Lift prims61 (primEnv61 N g), Ordinal.num2Lift prims61 (primEnv61 N g))

/-- Close Contender 61's language plus the tower of `S` from `c` as a family. -/
def metaStep (N : Nat) (g : Nat → Nat) (S : Closures → Closures) (c : Closures) : Closures :=
  (Ordinal.ptl2Lift (famTy :: prims61) (towerFrom S c, primEnv61 N g),
   Ordinal.num2Lift (famTy :: prims61) (towerFrom S c, primEnv61 N g))

/-- The hierarchy of step operators along a tree. -/
def metaS (N : Nat) (g : Nat → Nat) : CTree → Closures → Closures
  | .zero => step2 N g
  | .succ a => metaStep N g (metaS N g a)
  | .lim f => fun c =>
      (fun b t => .lim fun i => (metaS N g (f i) c).1 b t,
       fun h m => Ordinal.maxUpTo (fun i => (metaS N g (f i) c).2 h m) m)
  | .supL _ => step2 N g
  | .supH _ => step2 N g

/-- Contender 64's construction as a function of its input: `family64 42 = contender_64`. -/
def family64 (n : Nat) : Nat := F64 (F64 n)

/-- Contender 64's tree, joined with the meta-hierarchy's tree closure of the meta-jump. -/
def metaSTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then tower2Tree N
    else (towerFrom (metaS N family64 (tower2Tree N)) (base61 N family64) (tower2Tree N)).1
      (metaJump N) (tower2Tree N)

/-- The meta-hierarchy's number closure at meta-level and height `T`. -/
def metaSClosure (N : Nat) (g : Nat → Nat) (T : CTree) : Nat → Nat :=
  (towerFrom (metaS N g T) (base61 N g) T).2 g

/-- The hierarchy along the tree, based on the meta-hierarchy's number closure. -/
def F65 (n : Nat) : Nat :=
  Ordinal.hier (metaSClosure (family64 n) family64 (metaSTree (family64 n)))
    (metaSTree (family64 n)) (family64 n)

/-- **Contender 65.** Never evaluate it. -/
def contender_65 : Nat := F65 (F65 42)

end BusyLean
