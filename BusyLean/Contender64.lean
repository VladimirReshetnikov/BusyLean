import BusyLean.Contender63

/-!
# Contender 64: the stacking-operator step, towered along a tree

```
contender_64 := F64 (F64 42)
F64 n        := hier ((tower2 N family63 T).2 family63) T N
```

Contender 63 turns Contender 62's stack and its family-raising operator into
values of a larger language. That step can be repeated, and with closure pairs
the repetitions can be indexed by a tree:

* `stack2From P σ c` is Contender 62's stack started from the closure pair `c`;
* `step2 c` closes the language whose primitives are Contender 61's plus
  `stack2From … c` as a family and the operator raising families to stacks
  started from `c`;
* `tower2` iterates `step2` along a tree, pointwise at limits.

The tower runs along Contender 63's tree to build the tree `T`, then along `T`
for the number closure.

**Do not evaluate `contender_64`.**
-/

namespace BusyLean.Ordinal

/-- Contender 62's stack, started from the closure pair `c0`. -/
def stack2From (P : List PTL2.Ty) (σ : PTL2.Env P) (c0 : Closures) : CTree → Closures
  | .zero => c0
  | .succ a =>
      let c := stack2From P σ c0 a
      (ptl2Lift (BusyLean.closTy :: P) (c, σ), num2Lift (BusyLean.closTy :: P) (c, σ))
  | .lim f =>
      (fun b t => .lim fun i => (stack2From P σ c0 (f i)).1 b t,
       fun g m => maxUpTo (fun i => (stack2From P σ c0 (f i)).2 g m) m)
  | .supL _ => c0
  | .supH _ => c0

end BusyLean.Ordinal

namespace BusyLean

open Ordinal (CTree)

/-- One step: close Contender 61's language plus the stack started from `c` and its raising operator. -/
def step2 (N : Nat) (g : Nat → Nat) (c : Ordinal.Closures) : Ordinal.Closures :=
  let σ := primEnv61 N g
  let σ' : Ordinal.PTL2.Env prims63 :=
    (Ordinal.stack2From prims61 σ c,
     fun H => Ordinal.stack2From (famTy :: prims61) (H, σ) c, σ)
  (Ordinal.ptl2Lift prims63 σ', Ordinal.num2Lift prims63 σ')

/-- `step2` iterated along a tree. -/
def tower2 (N : Nat) (g : Nat → Nat) : CTree → Ordinal.Closures
  | .zero => (Ordinal.ptl2Lift prims61 (primEnv61 N g), Ordinal.num2Lift prims61 (primEnv61 N g))
  | .succ a => step2 N g (tower2 N g a)
  | .lim f =>
      (fun b t => .lim fun i => (tower2 N g (f i)).1 b t,
       fun h m => Ordinal.maxUpTo (fun i => (tower2 N g (f i)).2 h m) m)
  | .supL _ => (Ordinal.ptl2Lift prims61 (primEnv61 N g), Ordinal.num2Lift prims61 (primEnv61 N g))
  | .supH _ => (Ordinal.ptl2Lift prims61 (primEnv61 N g), Ordinal.num2Lift prims61 (primEnv61 N g))

/-- Contender 63's construction as a function of its input: `family63 42 = contender_63`. -/
def family63 (n : Nat) : Nat := F63 (F63 n)

/-- Contender 63's tree, joined with the tower's tree closure of the meta-jump along it. -/
def tower2Tree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then up2Tree N
    else (tower2 N family63 (up2Tree N)).1 (metaJump N) (up2Tree N)

/-- The tower's number closure along a tree. -/
def tower2Closure (N : Nat) (g : Nat → Nat) (T : CTree) : Nat → Nat := (tower2 N g T).2 g

/-- The hierarchy along the tree, based on the tower's number closure along it. -/
def F64 (n : Nat) : Nat :=
  Ordinal.hier (tower2Closure (family63 n) family63 (tower2Tree (family63 n)))
    (tower2Tree (family63 n)) (family63 n)

/-- **Contender 64.** Never evaluate it. -/
def contender_64 : Nat := F64 (F64 42)

end BusyLean
