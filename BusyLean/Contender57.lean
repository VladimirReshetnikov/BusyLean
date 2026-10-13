import BusyLean.Contender56

/-!
# Contender 57: stacking heights chosen by programs

```
contender_57 := F57 (F57 42)
F57 n        := hier (numLift prims57 (primEnv57 N family56) family56) (heightTree N) N
```

Contender 56's joint stack runs to heights fixed from outside. Here it is a
primitive at **any** height a program computes:

* `stackT : tree → (tree → tree) → tree → tree`, `stackT t = (jointStack … t).1`;
* `stackN : tree → (nat → nat) → nat → nat`, `stackN t = (jointStack … t).2`;

next to Contender 54's primitives (tree operators, iteration operators,
reflection, the number oracle). Programs build a height, for instance from
another stack's output, stack languages to it, and repeat at higher types. The
tree joins Contender 56's tree with the closure of the meta-jump under this
language. The number closure of the language is the hierarchy's base.

**Do not evaluate `contender_57`.**
-/

namespace BusyLean

open Ordinal (CTree)
open Ordinal.TL (Ty)

/-- The joint stack at a program-chosen height, then Contender 54's primitives. -/
def prims57 : List Ty :=
  .arr .tree Ordinal.liftTy :: .arr .tree Ordinal.liftNTy :: prims54

/-- The values of the primitives at depth `N` with number oracle `g`. -/
def primEnv57 (N : Nat) (g : Nat → Nat) : Ordinal.TL.Env prims57 :=
  (fun t => (Ordinal.jointStack prims54 (primEnv54 N g) t).1,
   fun t => (Ordinal.jointStack prims54 (primEnv54 N g) t).2,
   primEnv54 N g)

/-- Contender 56's construction as a function of its input: `family56 42 = contender_56`. -/
def family56 (n : Nat) : Nat := F56 (F56 n)

/-- Contender 56's tree, joined with the meta-jump's closure under the height-choosing language. -/
def heightTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then jointTree N
    else Ordinal.ptlLift prims57 (primEnv57 N family56) (metaJump N) (jointTree N)

/-- The hierarchy along the tree, based on the language's number closure. -/
def F57 (n : Nat) : Nat :=
  Ordinal.hier (Ordinal.numLift prims57 (primEnv57 (family56 n) family56) family56)
    (heightTree (family56 n)) (family56 n)

/-- **Contender 57.** Never evaluate it. -/
def contender_57 : Nat := F57 (F57 42)

end BusyLean
