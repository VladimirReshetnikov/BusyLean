import BusyLean.Contender66

/-!
# Contender 67: a reflective tower of closure operators

```
contender_67 := F67 (F67 42)
F67 n        := hier ((cwTower N family66 T (const61 N family66)).2 family66) T N
```

Contender 66's `closeWith` closes the *base* language with a family of
closures. Here the closing operator is itself raised along a tree:

* `cw 0 H` is the closure of Contender 66's language plus the family `H`;
* `cw (a+1) H` is the closure of the language that has, besides Contender 66's
  primitives and the family `H`, level `a`'s whole operator `cw a` as a
  primitive of type `(tree → C) → C`;
* limits are pointwise.

The primitive types are the same at every successor level, so one recursion on
the operator suffices. At level `a+1` programs can close level `a`'s language
with families they build, including towers of steps built from `cw a` itself.
Stacking (Contender 62) is the special case of a constant family.

**Do not evaluate `contender_67`.**
-/

namespace BusyLean

open Ordinal (CTree Closures)
open Ordinal.PTL2 (Ty)

/-- The type of closure-with-family operators. -/
def cwTy : Ty := .arr famTy closTy

/-- The reflective tower of closure operators along a tree. -/
def cwTower (N : Nat) (g : Nat → Nat) : CTree → (CTree → Closures) → Closures
  | .zero => fun H =>
      (Ordinal.ptl2Lift (famTy :: prims66) (H, primEnv66 N g),
       Ordinal.num2Lift (famTy :: prims66) (H, primEnv66 N g))
  | .succ a => fun H =>
      (Ordinal.ptl2Lift (famTy :: cwTy :: prims66) (H, cwTower N g a, primEnv66 N g),
       Ordinal.num2Lift (famTy :: cwTy :: prims66) (H, cwTower N g a, primEnv66 N g))
  | .lim f => fun H =>
      (fun b t => .lim fun i => (cwTower N g (f i) H).1 b t,
       fun h m => Ordinal.maxUpTo (fun i => (cwTower N g (f i) H).2 h m) m)
  | .supL _ => fun H =>
      (Ordinal.ptl2Lift (famTy :: prims66) (H, primEnv66 N g),
       Ordinal.num2Lift (famTy :: prims66) (H, primEnv66 N g))
  | .supH _ => fun H =>
      (Ordinal.ptl2Lift (famTy :: prims66) (H, primEnv66 N g),
       Ordinal.num2Lift (famTy :: prims66) (H, primEnv66 N g))

/-- The constant family of Contender 61's base closures. -/
def const61 (N : Nat) (g : Nat → Nat) : CTree → Closures := fun _ => base61 N g

/-- Contender 66's construction as a function of its input: `family66 42 = contender_66`. -/
def family66 (n : Nat) : Nat := F66 (F66 n)

/-- Contender 66's tree, joined with the tower's tree closure of the meta-jump at height equal to it. -/
def cwTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then closeTree N
    else (cwTower N family66 (closeTree N) (const61 N family66)).1 (metaJump N) (closeTree N)

/-- The tower's number closure at height `T`. -/
def cwClosure (N : Nat) (g : Nat → Nat) (T : CTree) : Nat → Nat := (cwTower N g T (const61 N g)).2 g

/-- The hierarchy along the tree, based on the tower's number closure at height equal to it. -/
def F67 (n : Nat) : Nat :=
  Ordinal.hier (cwClosure (family66 n) family66 (cwTree (family66 n))) (cwTree (family66 n)) (family66 n)

/-- **Contender 67.** Never evaluate it. -/
def contender_67 : Nat := F67 (F67 42)

end BusyLean
