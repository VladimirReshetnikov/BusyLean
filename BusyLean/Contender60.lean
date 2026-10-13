import BusyLean.Contender59

/-!
# Contender 60: a hierarchy of tower operators

```
contender_60 := F60 (F60 42)
F60 n        := hier ((upLevels prims54 (primEnv54 N family59) T T).2 family59) T N
```

Contender 59's tower `towerT` is a height-indexed family of closure pairs. A
tower can carry such a family `H` as extra primitives: `towerH P σ H` is
Contender 59's tower whose languages also contain `H t` for every
program-chosen height `t`. Iterating `H ↦ towerH H` along a tree gives a
hierarchy of tower operators:

* `upLevels 0 = towerT`;
* `upLevels (k+1) = towerH (upLevels k)`: towers whose languages contain the
  previous level's towers, at every height;
* limits are pointwise.

The level, the height and the argument are all Contender 59's tree. The result
builds the tree and then reads it.

**Do not evaluate `contender_60`.**
-/

namespace BusyLean.Ordinal

/-- `towerStep` with an extra height-indexed family of closures as primitives. -/
def towerStepH (P : List TL.Ty) (σ : TL.Env P) (H : CTree → Closures) (c : Closures) : Closures :=
  let P' := TL.Ty.arr .tree liftTy :: TL.Ty.arr .tree liftNTy ::
    TL.Ty.arr .tree liftTy :: TL.Ty.arr .tree liftNTy :: P
  let σ' : TL.Env P' := (fun t => (jointFrom P σ c t).1, fun t => (jointFrom P σ c t).2,
    fun t => (H t).1, fun t => (H t).2, σ)
  (ptlLift P' σ', numLift P' σ')

/-- The tower whose languages also contain the family `H`. -/
def towerH (P : List TL.Ty) (σ : TL.Env P) (H : CTree → Closures) : CTree → Closures
  | .zero => (ptlLift P σ, numLift P σ)
  | .succ a => towerStepH P σ H (towerH P σ H a)
  | .lim f =>
      (fun b t => .lim fun i => (towerH P σ H (f i)).1 b t,
       fun g m => maxUpTo (fun i => (towerH P σ H (f i)).2 g m) m)
  | .supL _ => (ptlLift P σ, numLift P σ)
  | .supH _ => (ptlLift P σ, numLift P σ)

/-- The hierarchy of tower operators along a tree. -/
def upLevels (P : List TL.Ty) (σ : TL.Env P) : CTree → CTree → Closures
  | .zero => towerT P σ
  | .succ k => towerH P σ (upLevels P σ k)
  | .lim f => fun t =>
      (fun b s => .lim fun i => (upLevels P σ (f i) t).1 b s,
       fun g m => maxUpTo (fun i => (upLevels P σ (f i) t).2 g m) m)
  | .supL _ => towerT P σ
  | .supH _ => towerT P σ

end BusyLean.Ordinal

namespace BusyLean

open Ordinal (CTree)

/-- Contender 59's construction as a function of its input: `family59 42 = contender_59`. -/
def family59 (n : Nat) : Nat := F59 (F59 n)

/-- Contender 59's tree, joined with the tree closure of the hierarchy at level and height equal to it. -/
def upTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then towerTreeT N
    else (Ordinal.upLevels prims54 (primEnv54 N family59) (towerTreeT N) (towerTreeT N)).1
      (metaJump N) (towerTreeT N)

/-- The hierarchy's number closure at level and height `T`. -/
def upClosure (N : Nat) (g : Nat → Nat) (T : CTree) : Nat → Nat :=
  (Ordinal.upLevels prims54 (primEnv54 N g) T T).2 g

/-- The hierarchy along the tree, based on the number closure at level and height equal to it. -/
def F60 (n : Nat) : Nat :=
  Ordinal.hier (upClosure (family59 n) family59 (upTree (family59 n))) (upTree (family59 n)) (family59 n)

/-- **Contender 60.** Never evaluate it. -/
def contender_60 : Nat := F60 (F60 42)

end BusyLean
