import BusyLean.Contender69

/-!
# Contender 70: the reflection cycle repeated

```
contender_70 := F70 (F70 42)
F70 n        := hier (cycleClosure N family69 T) T N
```

Contenders 67 and 68 form a cycle: raise a language's closure operator along a
tree (`cwTowerP`), then add that tower's step and the tower itself as values,
which gives a stronger language. Contender 69 started the cycle again. Here it
is repeated `N` times:

* `primsR 0` is Contender 66's language;
* `primsR (k+1)` adds `cwStep` and `cwAt` for the reflective tower **over level
  `k`'s language**.

The reflective tower over the top language runs along Contender 69's tree to
build the tree `T`, then along `T` for the number closure. The cycle count is
`N = family69 n`.

**Do not evaluate `contender_70`.**
-/

namespace BusyLean

open Ordinal (CTree Closures)
open Ordinal.PTL2 (Ty)

/-- One level of the reflective tower over any base language, from any operator `X`. -/
def cwStepP (P : List Ty) (σ : Ordinal.PTL2.Env P) (X : (CTree → Closures) → Closures)
    (H : CTree → Closures) : Closures :=
  (Ordinal.ptl2Lift (famTy :: cwTy :: P) (H, X, σ), Ordinal.num2Lift (famTy :: cwTy :: P) (H, X, σ))

/-- The primitive types after `k` cycles. -/
def primsR : Nat → List Ty
  | 0 => prims66
  | k + 1 => .arr cwTy cwTy :: .arr .tree cwTy :: primsR k

/-- The primitive values after `k` cycles. -/
def envR (N : Nat) (g : Nat → Nat) : (k : Nat) → Ordinal.PTL2.Env (primsR k)
  | 0 => primEnv66 N g
  | k + 1 => (cwStepP (primsR k) (envR N g k), cwTowerP (primsR k) (envR N g k), envR N g k)

/-- The reflective tower over the language after `N` cycles. -/
def cycleTower (N : Nat) (g : Nat → Nat) (T : CTree) : Closures :=
  cwTowerP (primsR N) (envR N g N) T (const61 N g)

/-- Contender 69's construction as a function of its input: `family69 42 = contender_69`. -/
def family69 (n : Nat) : Nat := F69 (F69 n)

/-- Contender 69's tree, joined with the top tower's tree closure of the meta-jump. -/
def cycleTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then cwTreeP N
    else (cycleTower N family69 (cwTreeP N)).1 (metaJump N) (cwTreeP N)

/-- The top tower's number closure at height `T`. -/
def cycleClosure (N : Nat) (g : Nat → Nat) (T : CTree) : Nat → Nat := (cycleTower N g T).2 g

/-- The hierarchy along the tree, based on the top tower's number closure. -/
def F70 (n : Nat) : Nat :=
  Ordinal.hier (cycleClosure (family69 n) family69 (cycleTree (family69 n))) (cycleTree (family69 n))
    (family69 n)

/-- **Contender 70.** Never evaluate it. -/
def contender_70 : Nat := F70 (F70 42)

end BusyLean
