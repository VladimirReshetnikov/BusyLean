import BusyLean.Contender62

/-!
# Contender 63: programs over the stacking operator of the tower language

```
contender_63 := F63 (F63 42)
F63 n        := hier (up2Closure N family62) (up2Tree N) N
```

Contender 62 stacks Contender 61's language along a tree. With products, the
step of Contenders 59-61 (stack along any height, add a family of closures as
primitives, make the operator a value) fits in one language:

* `stack2Fam : tree → C`, Contender 62's stack at any height;
* `up2 : (tree → C) → tree → C`, `up2 H` = the stack whose languages also
  contain the family `H` as a primitive.

So hierarchies `up2 (up2 (… stack2Fam))`, iterated along trees that programs
build, are programs. These two primitives join Contender 61's. The tree joins
Contender 62's tree with the meta-jump's closure under this language, whose
number closure is the hierarchy's base.

**Do not evaluate `contender_63`.**
-/

namespace BusyLean

open Ordinal (CTree)
open Ordinal.PTL2 (Ty)

/-- The stack of Contender 61's language whose languages also contain the family `H`. -/
def up2 (N : Nat) (g : Nat → Nat) (H : CTree → Ordinal.Closures) : CTree → Ordinal.Closures :=
  Ordinal.stack2 (famTy :: prims61) (H, primEnv61 N g)

/-- Contender 61's primitives plus the stack and its family-raising operator. -/
def prims63 : List Ty := famTy :: .arr famTy famTy :: prims61

def primEnv63 (N : Nat) (g : Nat → Nat) : Ordinal.PTL2.Env prims63 :=
  (Ordinal.stack2 prims61 (primEnv61 N g), up2 N g, primEnv61 N g)

/-- Contender 62's construction as a function of its input: `family62 42 = contender_62`. -/
def family62 (n : Nat) : Nat := F62 (F62 n)

/-- Contender 62's tree, joined with the meta-jump's closure under the language. -/
def up2Tree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then stack2Tree N
    else Ordinal.ptl2Lift prims63 (primEnv63 N family62) (metaJump N) (stack2Tree N)

/-- The language's number closure over the oracle `g`. -/
def up2Closure (N : Nat) (g : Nat → Nat) : Nat → Nat :=
  Ordinal.num2Lift prims63 (primEnv63 N g) g

/-- The hierarchy along the tree, based on the language's number closure. -/
def F63 (n : Nat) : Nat :=
  Ordinal.hier (up2Closure (family62 n) family62) (up2Tree (family62 n)) (family62 n)

/-- **Contender 63.** Never evaluate it. -/
def contender_63 : Nat := F63 (F63 42)

end BusyLean
