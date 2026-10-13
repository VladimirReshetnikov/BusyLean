import BusyLean.Ordinal.TreeLanguage4
import BusyLean.Contender37

/-!
# Contender 38: a first-class operator meta-language over the ladder-jump stack

```
family37 n   := F37 (F37 n)          -- family37 42 = contender_37
F38 n        := wDiagonalLift (schedule38 n) (rank38 n)
                  om38Transformer (fun _ => family37) n n
contender_38 := F38 (F38 42)
```

Contender 37 stacks the tree language over a ladder-bootstrap jump, but the
operation that closes a whole tree language is still external to the object
language.  Contender 38 internalizes that operation as a first-class constant

```
lang : (tree -> tree) -> (tree -> tree)
```

inside a total simply typed meta-language.  Programs may abstract over,
compose, pass, and recursively iterate language constructors at arbitrary
simple types.  The whole operator language is then closed and stacked along
Contender 37's `jumpTree`.

The semantic seed retains the current champion's mechanisms at a stronger
oracle: one branch bootstraps a tree along itself using `family37`, and another
stacks the inherited tree language over that jump to height `jumpTree n`.
The new operator language is closed over this hybrid seed and then iterated
along the same predecessor tree.

**Do not evaluate `contender_38`.**
-/

namespace BusyLean

/-- Contender 37's construction as an input-indexed family.
At input 42 this unfolds to `contender_37`. -/
def family37 (n : Nat) : Nat := F37 (F37 n)

/-- The ladder jump, now run with the full Contender 37 family as oracle. -/
def predecessorJump38 (n : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  FLT.bootT family37 n t t

/--
The primitive operator exposed to the new meta-language.  Branch zero is the
predecessor-seeded ladder jump.  Every positive branch stacks the inherited
whole tree language over that jump along Contender 37's `jumpTree`.
-/
def operatorSeed38 (n : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then predecessorJump38 n t
    else Ordinal.stackOver (predecessorJump38 n) (jumpTree n) t

/--
The new tree at input `n`.  Its first branch is the complete Contender 37 tree.
The other branches stack the entire first-class operator language, using
`jumpTree n` both as the stack height and the argument.
-/
def operatorMetaTree38 (n : Nat) : Ordinal.CTree :=
  let T := jumpTree n
  .lim fun i =>
    if i = 0 then T
    else Ordinal.operatorBoostT (operatorSeed38 n) T T

end BusyLean

namespace BusyLean.FL

open Ordinal

/-- Typed ladder programs over the new tree are strongly normalizing. -/
theorem sn_erase_om38tree {f : Nat -> Nat} (L : Nat) {fuel : Nat}
    {t : CTm (Addr (operatorMetaTree38 L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (operatorMetaTree38 L)))
    (infer_sound fuel t (goodCtx_nil []) h).1

/-- Value of a type-checked ladder program over `operatorMetaTree38 L`. -/
def om38value (L : Nat) (f : Nat -> Nat) (fuel : Nat)
    (t : CTm (Addr (operatorMetaTree38 L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_om38tree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth at most `n` over addresses of the input-`n` tree. -/
def om38LadderUpTo (n : Nat) : List (CTm (Addr (operatorMetaTree38 n))) :=
  ctmsUpTo (addrUpTo (operatorMetaTree38 n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Reflection over an oracle family and the operator-meta-language ladder. -/
def reflectOM38Family (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.om38value n (packFamily fs) n) (FL.om38LadderUpTo n))

/-- The progressive transformer induced by `reflectOM38Family`. -/
def om38Transformer : Transformer := fun fs _ n => reflectOM38Family fs n

/-- Autonomous schedule above the predecessor's schedule. -/
def schedule38 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family37 n + 42) (Autonomous.encode (schedule37 n)))

/-- A second autonomous expansion supplies the W-rank tree. -/
def rank38 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family37 n + 42) (Autonomous.encode (schedule38 n)))

/-- W-ranked hyperreflection over operator-meta-language address ladders. -/
def F38 (n : Nat) : Nat :=
  wDiagonalLift (schedule38 n) (rank38 n) om38Transformer (fun _ => family37) n n

/-- **Contender 38.** Never evaluate it. -/
def contender_38 : Nat := F38 (F38 42)

end BusyLean
