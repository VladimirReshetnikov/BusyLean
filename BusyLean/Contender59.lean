import BusyLean.Contender58

/-!
# Contender 59: the tower of stack-reflecting languages along a tree

```
contender_59 := F59 (F59 42)
F59 n        := hier ((towerT prims54 (primEnv54 N family58) T).2 family58) T N
```

Contender 58's tower has a natural-number height, because primitive lists are
finite. Working with closure pairs instead of primitive lists, the tower can
be indexed by a tree:

* `jointFrom P σ c0` is Contender 56's joint stack started from the closure
  pair `c0` (level 0 is `c0`, not the closure of `P`);
* `towerStep P σ c` closes the language whose primitives are `P` plus the
  height-indexed joint stacks started from `c`;
* `towerT P σ` iterates `towerStep` along a tree, pointwise at limits.

The tower runs along Contender 58's tree to build the tree `T`, then along `T`
for the number closure.

**Do not evaluate `contender_59`.**
-/

namespace BusyLean.Ordinal

/-- The joint stack started from the closure pair `c0`. -/
def jointFrom (P : List TL.Ty) (σ : TL.Env P) (c0 : Closures) : CTree → Closures
  | .zero => c0
  | .succ a =>
      let c := jointFrom P σ c0 a
      (ptlLift (liftTy :: liftNTy :: P) (c.1, c.2, σ), numLift (liftTy :: liftNTy :: P) (c.1, c.2, σ))
  | .lim f =>
      (fun b t => .lim fun i => (jointFrom P σ c0 (f i)).1 b t,
       fun g m => maxUpTo (fun i => (jointFrom P σ c0 (f i)).2 g m) m)
  | .supL _ => c0
  | .supH _ => c0

/-- Close the language `P` plus the height-indexed joint stacks started from `c`. -/
def towerStep (P : List TL.Ty) (σ : TL.Env P) (c : Closures) : Closures :=
  let P' := TL.Ty.arr .tree liftTy :: TL.Ty.arr .tree liftNTy :: P
  let σ' : TL.Env P' := (fun t => (jointFrom P σ c t).1, fun t => (jointFrom P σ c t).2, σ)
  (ptlLift P' σ', numLift P' σ')

/-- The tower of stack-reflecting languages along a tree. -/
def towerT (P : List TL.Ty) (σ : TL.Env P) : CTree → Closures
  | .zero => (ptlLift P σ, numLift P σ)
  | .succ a => towerStep P σ (towerT P σ a)
  | .lim f =>
      (fun b t => .lim fun i => (towerT P σ (f i)).1 b t,
       fun g m => maxUpTo (fun i => (towerT P σ (f i)).2 g m) m)
  | .supL _ => (ptlLift P σ, numLift P σ)
  | .supH _ => (ptlLift P σ, numLift P σ)

end BusyLean.Ordinal

namespace BusyLean

open Ordinal (CTree)

/-- Contender 58's construction as a function of its input: `family58 42 = contender_58`. -/
def family58 (n : Nat) : Nat := F58 (F58 n)

/-- Contender 58's tree, joined with the tower's tree closure of the meta-jump along it. -/
def towerTreeT (N : Nat) : CTree :=
  .lim fun i => if i = 0 then towerTree N
    else (Ordinal.towerT prims54 (primEnv54 N family58) (towerTree N)).1 (metaJump N) (towerTree N)

/-- The tower's number closure along a tree. -/
def towerClosureT (N : Nat) (g : Nat → Nat) (T : CTree) : Nat → Nat :=
  (Ordinal.towerT prims54 (primEnv54 N g) T).2 g

/-- The hierarchy along the tree, based on the tower's number closure along it. -/
def F59 (n : Nat) : Nat :=
  Ordinal.hier (towerClosureT (family58 n) family58 (towerTreeT (family58 n)))
    (towerTreeT (family58 n)) (family58 n)

/-- **Contender 59.** Never evaluate it. -/
def contender_59 : Nat := F59 (F59 42)

end BusyLean
