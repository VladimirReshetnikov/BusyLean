import BusyLean.Contender68

/-!
# Contender 69: the reflective tower over the step language

```
contender_69 := F69 (F69 42)
F69 n        := hier ((cwTowerP prims68 (primEnv68 N family68) T (const61 N family68)).2 family68) T N
```

Contender 67 raised the closure operator of Contender 66's language along a
tree. Contender 68's language is stronger: it contains that tower's step and
the tower itself as values. `cwTowerP P σ` is Contender 67's construction for
any base language `(P, σ)`:

* level 0 closes the base language plus a family `H`;
* level `a+1` closes the base language plus `H` and level `a`'s whole operator
  `(tree → C) → C`;
* limits are pointwise.

Contender 69 runs it over Contender 68's language, along Contender 68's tree.

**Do not evaluate `contender_69`.**
-/

namespace BusyLean

open Ordinal (CTree Closures)
open Ordinal.PTL2 (Ty)

/-- Contender 67's reflective tower of closure operators over any base language. -/
def cwTowerP (P : List Ty) (σ : Ordinal.PTL2.Env P) : CTree → (CTree → Closures) → Closures
  | .zero => fun H =>
      (Ordinal.ptl2Lift (famTy :: P) (H, σ), Ordinal.num2Lift (famTy :: P) (H, σ))
  | .succ a => fun H =>
      (Ordinal.ptl2Lift (famTy :: cwTy :: P) (H, cwTowerP P σ a, σ),
       Ordinal.num2Lift (famTy :: cwTy :: P) (H, cwTowerP P σ a, σ))
  | .lim f => fun H =>
      (fun b t => .lim fun i => (cwTowerP P σ (f i) H).1 b t,
       fun h m => Ordinal.maxUpTo (fun i => (cwTowerP P σ (f i) H).2 h m) m)
  | .supL _ => fun H =>
      (Ordinal.ptl2Lift (famTy :: P) (H, σ), Ordinal.num2Lift (famTy :: P) (H, σ))
  | .supH _ => fun H =>
      (Ordinal.ptl2Lift (famTy :: P) (H, σ), Ordinal.num2Lift (famTy :: P) (H, σ))

/-- Contender 68's construction as a function of its input: `family68 42 = contender_68`. -/
def family68 (n : Nat) : Nat := F68 (F68 n)

/-- Contender 68's tree, joined with the tower's tree closure of the meta-jump at height equal to it. -/
def cwTreeP (N : Nat) : CTree :=
  .lim fun i => if i = 0 then cwStepTree N
    else (cwTowerP prims68 (primEnv68 N family68) (cwStepTree N) (const61 N family68)).1
      (metaJump N) (cwStepTree N)

/-- The tower's number closure at height `T`. -/
def cwClosureP (N : Nat) (g : Nat → Nat) (T : CTree) : Nat → Nat :=
  (cwTowerP prims68 (primEnv68 N g) T (const61 N g)).2 g

/-- The hierarchy along the tree, based on the tower's number closure at height equal to it. -/
def F69 (n : Nat) : Nat :=
  Ordinal.hier (cwClosureP (family68 n) family68 (cwTreeP (family68 n))) (cwTreeP (family68 n))
    (family68 n)

/-- **Contender 69.** Never evaluate it. -/
def contender_69 : Nat := F69 (F69 42)

end BusyLean
