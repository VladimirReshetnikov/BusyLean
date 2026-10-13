import BusyLean.Contender61

/-!
# Contender 62: the tower language stacked along a tree

```
contender_62 := F62 (F62 42)
F62 n        := hier ((stack2 prims61 (primEnv61 N family61) T).2 family61) T N
```

Contender 61's language over the tower operators has products, so a whole
closure pair `C` is a single value. `stack2` stacks this language along a tree:

* level 0 is the language's closure pair (`ptl2Lift`, `num2Lift`);
* level `a+1`'s language has level `a`'s closure pair as one extra primitive of
  type `C`, so programs can apply both closures, compose them and iterate them
  at higher types;
* limits are pointwise for trees and maxima for numbers.

The stack runs along Contender 61's tree to build the tree `T`, then along `T`
for the number closure.

**Do not evaluate `contender_62`.**
-/

namespace BusyLean.Ordinal

/-- The language over `P` stacked along a tree, each level's closure pair a primitive of the next. -/
def stack2 (P : List PTL2.Ty) (σ : PTL2.Env P) : CTree → Closures
  | .zero => (ptl2Lift P σ, num2Lift P σ)
  | .succ a =>
      let c := stack2 P σ a
      (ptl2Lift (BusyLean.closTy :: P) (c, σ), num2Lift (BusyLean.closTy :: P) (c, σ))
  | .lim f =>
      (fun b t => .lim fun i => (stack2 P σ (f i)).1 b t,
       fun g m => maxUpTo (fun i => (stack2 P σ (f i)).2 g m) m)
  | .supL _ => (ptl2Lift P σ, num2Lift P σ)
  | .supH _ => (ptl2Lift P σ, num2Lift P σ)

end BusyLean.Ordinal

namespace BusyLean

open Ordinal (CTree)

/-- Contender 61's construction as a function of its input: `family61 42 = contender_61`. -/
def family61 (n : Nat) : Nat := F61 (F61 n)

/-- Contender 61's tree, joined with the stacked tree closure of the meta-jump along it. -/
def stack2Tree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then towerProgTree N
    else (Ordinal.stack2 prims61 (primEnv61 N family61) (towerProgTree N)).1 (metaJump N)
      (towerProgTree N)

/-- The stacked number closure along a tree. -/
def stack2Closure (N : Nat) (g : Nat → Nat) (T : CTree) : Nat → Nat :=
  (Ordinal.stack2 prims61 (primEnv61 N g) T).2 g

/-- The hierarchy along the tree, based on the stacked number closure along it. -/
def F62 (n : Nat) : Nat :=
  Ordinal.hier (stack2Closure (family61 n) family61 (stack2Tree (family61 n)))
    (stack2Tree (family61 n)) (family61 n)

/-- **Contender 62.** Never evaluate it. -/
def contender_62 : Nat := F62 (F62 42)

end BusyLean
