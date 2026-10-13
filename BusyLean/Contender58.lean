import BusyLean.Contender57

/-!
# Contender 58: a tower of stack-reflecting languages

```
contender_58 := F58 (F58 42)
F58 n        := hier (towerClosure N family57) (towerTree N) N
```

Contender 57 turns the joint stack over a language into primitives of a larger
language. The step can be repeated:

* `primsK 0 = prims54` with Contender 54's environment;
* `primsK (k+1)` adds `stackT, stackN` for the joint stack **over the language
  of level `k`**, at any program-chosen height.

Level `k+1`'s programs can thus stack, at heights they choose, languages that
themselves stack languages, `k` levels deep. The tower height is `N`, the
previous family's value. The tree joins Contender 57's tree with the closure of
the meta-jump under the top language, whose number closure is the hierarchy's
base.

**Do not evaluate `contender_58`.**
-/

namespace BusyLean

open Ordinal (CTree)
open Ordinal.TL (Ty)

/-- The primitive types of level `k` of the tower. -/
def primsK : Nat → List Ty
  | 0 => prims54
  | k + 1 => .arr .tree Ordinal.liftTy :: .arr .tree Ordinal.liftNTy :: primsK k

/-- The primitive values of level `k`: each level adds the joint stack over the previous one. -/
def envK (N : Nat) (g : Nat → Nat) : (k : Nat) → Ordinal.TL.Env (primsK k)
  | 0 => primEnv54 N g
  | k + 1 =>
      (fun t => (Ordinal.jointStack (primsK k) (envK N g k) t).1,
       fun t => (Ordinal.jointStack (primsK k) (envK N g k) t).2,
       envK N g k)

/-- Contender 57's construction as a function of its input: `family57 42 = contender_57`. -/
def family57 (n : Nat) : Nat := F57 (F57 n)

/-- Contender 57's tree, joined with the meta-jump's closure under the level-`N` language. -/
def towerTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then heightTree N
    else Ordinal.ptlLift (primsK N) (envK N family57 N) (metaJump N) (heightTree N)

/-- The number closure of the level-`N` language over the oracle `g`. -/
def towerClosure (N : Nat) (g : Nat → Nat) : Nat → Nat :=
  Ordinal.numLift (primsK N) (envK N g N) g

/-- The hierarchy along the tree, based on the level-`N` language's number closure. -/
def F58 (n : Nat) : Nat :=
  Ordinal.hier (towerClosure (family57 n) family57) (towerTree (family57 n)) (family57 n)

/-- **Contender 58.** Never evaluate it. -/
def contender_58 : Nat := F58 (F58 42)

end BusyLean
