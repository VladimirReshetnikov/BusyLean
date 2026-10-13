import BusyLean.Contender55

/-!
# Contender 56: tree and number languages stacked jointly

```
contender_56 := F56 (F56 42)
F56 n        := hier ((jointStack prims54 (primEnv54 N family55) T').2 family55) T' N
```

Contenders 52 and 55 stack tree languages and number languages separately.
Contender 55's number programs build trees only with Contender 51's fixed
operators, never with the stacked tree languages. `jointStack` stacks both
closures together. Level `a+1`'s language has as primitives **both** of level
`a`'s closures:

* `liftT : (tree → tree) → tree → tree`, the tree closure, and
* `liftN : (nat → nat) → nat → nat`, the number closure.

So a number program at level `a+1` can build trees with the whole level-`a`
tree language, reflect over them (`reflT`), and close number functions under
level `a`'s number language. Limits are pointwise for trees and maxima for
numbers. The joint stack first builds the tree `T'` along Contender 52's tree,
then runs along `T'` and reads it.

**Do not evaluate `contender_56`.**
-/

namespace BusyLean.Ordinal

/-- A pair of closures: on tree operators and on number functions. -/
abbrev Closures := ((CTree → CTree) → CTree → CTree) × ((Nat → Nat) → Nat → Nat)

/-- Tree and number languages stacked jointly along a tree. -/
def jointStack (P : List TL.Ty) (σ : TL.Env P) : CTree → Closures
  | .zero => (ptlLift P σ, numLift P σ)
  | .succ a =>
      let c := jointStack P σ a
      (ptlLift (liftTy :: liftNTy :: P) (c.1, c.2, σ), numLift (liftTy :: liftNTy :: P) (c.1, c.2, σ))
  | .lim f =>
      (fun b t => .lim fun i => (jointStack P σ (f i)).1 b t,
       fun g m => maxUpTo (fun i => (jointStack P σ (f i)).2 g m) m)
  | .supL _ => (ptlLift P σ, numLift P σ)
  | .supH _ => (ptlLift P σ, numLift P σ)

end BusyLean.Ordinal

namespace BusyLean

open Ordinal (CTree)

/-- Contender 55's construction as a function of its input: `family55 42 = contender_55`. -/
def family55 (n : Nat) : Nat := F55 (F55 n)

/-- The tree built by the joint stack along Contender 52's tree, over the meta-jump. -/
def jointTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then stackTree N
    else (Ordinal.jointStack prims54 (primEnv54 N family55) (stackTree N)).1 (metaJump N) (stackTree N)

/-- The hierarchy along the joint tree, based on the joint number closure along it. -/
def F56 (n : Nat) : Nat :=
  Ordinal.hier
    ((Ordinal.jointStack prims54 (primEnv54 (family55 n) family55) (jointTree (family55 n))).2 family55)
    (jointTree (family55 n)) (family55 n)

/-- **Contender 56.** Never evaluate it. -/
def contender_56 : Nat := F56 (F56 42)

end BusyLean
