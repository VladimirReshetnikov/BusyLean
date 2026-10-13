import BusyLean.Ordinal.TreeLanguage4
import BusyLean.Contender36

/-!
# Contender 37: a first-class operator meta-language over the self-building ladder tree

```
family36 n   := F36 (F36 n)          -- family36 42 = contender_36
F37 n        := wDiagonalLift (schedule37 n) (rank37 n)
                  omTransformer (fun _ => family36) n n
contender_37 := F37 (F37 42)
```

Contender 36 lets ladder programs build the length of the next ladder, but the
operation that closes a whole tree language remains external to the object
language.  Contender 37 internalizes that operation as a first-class constant

```
lang : (tree -> tree) -> (tree -> tree)
```

inside a total simply typed meta-language.  Programs may abstract over,
compose, and recursively iterate language constructors at arbitrary simple
types.  The whole operator language is then stacked along Contender 36's
`bootTree`.

The seed operator is deliberately hybrid: one branch is Contender 36's current
ladder-bootstrap step, and one branch is the earlier whole-language stack at
height `bootTree n`.  Thus the new stage retains both the current champion's
self-building ladder mechanism and the previous tree-language closure before
closing under arbitrary operator programs.

**Do not evaluate `contender_37`.**
-/

namespace BusyLean

/-- Contender 36's construction as an input-indexed family.
At input 42 this unfolds to `contender_36`. -/
def family36 (n : Nat) : Nat := F36 (F36 n)

/--
The primitive operator exposed to the new meta-language.  Branch zero performs
one current ladder-bootstrap step over the argument tree.  Every positive
branch applies the old transfinite whole-language stack, now indexed by
Contender 36's tree.
-/
def operatorSeed37 (n : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then FLT.ladderTree family36 n t
    else Ordinal.boostT (bootTree n) t

/--
The new tree at input `n`.  Its first branch is the complete Contender 36 tree.
The other branches stack the entire first-class operator language, using
`bootTree n` both as the stack height and the argument.
-/
def operatorMetaTree (n : Nat) : Ordinal.CTree :=
  let T := bootTree n
  .lim fun i =>
    if i = 0 then T
    else Ordinal.operatorBoostT (operatorSeed37 n) T T

end BusyLean

namespace BusyLean.FL

open Ordinal

/-- Typed ladder programs over the new tree are strongly normalizing. -/
theorem sn_erase_omtree {f : Nat -> Nat} (L : Nat) {fuel : Nat}
    {t : CTm (Addr (operatorMetaTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (operatorMetaTree L)))
    (infer_sound fuel t (goodCtx_nil []) h).1

/-- Value of a type-checked ladder program over `operatorMetaTree L`. -/
def omvalue (L : Nat) (f : Nat -> Nat) (fuel : Nat)
    (t : CTm (Addr (operatorMetaTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_omtree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth at most `n` over addresses of the input-`n` tree. -/
def omLadderUpTo (n : Nat) : List (CTm (Addr (operatorMetaTree n))) :=
  ctmsUpTo (addrUpTo (operatorMetaTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Reflection over an oracle family and the operator-meta-language ladder. -/
def reflectOMFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.omvalue n (packFamily fs) n) (FL.omLadderUpTo n))

/-- The progressive transformer induced by `reflectOMFamily`. -/
def omTransformer : Transformer := fun fs _ n => reflectOMFamily fs n

/-- Autonomous schedule above the predecessor's schedule. -/
def schedule37 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family36 n + 42) (Autonomous.encode (schedule36 n)))

/-- A second autonomous expansion supplies the W-rank tree. -/
def rank37 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family36 n + 42) (Autonomous.encode (schedule37 n)))

/-- W-ranked hyperreflection over operator-meta-language address ladders. -/
def F37 (n : Nat) : Nat :=
  wDiagonalLift (schedule37 n) (rank37 n) omTransformer (fun _ => family36) n n

/-- **Contender 37.** Never evaluate it. -/
def contender_37 : Nat := F37 (F37 42)

end BusyLean
