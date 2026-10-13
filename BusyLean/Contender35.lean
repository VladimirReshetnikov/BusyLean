import BusyLean.Ordinal.TreeLanguage4
import BusyLean.Contender34

/-!
# Contender 35: an operator meta-language stacked along a tree ordinal

```
family34 n   := F34 (F34 n)          -- family34 42 = contender_34
F35 n        := wDiagonalLift (schedule35 n) (rank35 n)
                  osTransformer (fun _ => family34) n n
contender_35 := F35 (F35 42)
```

Contender 34 externally iterated the operation "make the whole language the
next primitive" along a tree ordinal.  Here that operation is internalized as
`OML.Tm.lang`, a primitive of type
`(tree -> tree) -> (tree -> tree)`.  The resulting operator meta-language can
abstract over, compose and recursively iterate language constructors.  The
entire meta-language is then stacked along Contender 34's own tree.

The outer amplifier remains the W-ranked hyperreflection hierarchy, now seeded
with Contender 34's family.  Do not evaluate `contender_35`.
-/

namespace BusyLean.FL

open Ordinal

/-- Typed ladder programs over the new tree are strongly normalizing. -/
theorem sn_erase_ostree {f : Nat -> Nat} (L : Nat) {fuel : Nat}
    {t : CTm (Addr (operatorStackedTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (operatorStackedTree L)))
    (infer_sound fuel t (goodCtx_nil []) h).1

/-- Value of a type-checked ladder program over `operatorStackedTree L`. -/
def osvalue (L : Nat) (f : Nat -> Nat) (fuel : Nat)
    (t : CTm (Addr (operatorStackedTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_ostree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth at most `n` over addresses of the input-`n` tree. -/
def ostreeLadderUpTo (n : Nat) : List (CTm (Addr (operatorStackedTree n))) :=
  ctmsUpTo (addrUpTo (operatorStackedTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Reflection over an oracle family and the new operator-stacked ladder. -/
def reflectOSFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.osvalue n (packFamily fs) n) (FL.ostreeLadderUpTo n))

/-- The progressive transformer induced by `reflectOSFamily`. -/
def osTransformer : Transformer := fun fs _ n => reflectOSFamily fs n

/-- Contender 34's construction as an input-indexed family. -/
def family34 (n : Nat) : Nat := F34 (F34 n)

/-- Autonomous schedule for the new W-ranked lift. -/
def schedule35 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family34 n + 42) (Autonomous.encode (schedule34 n)))

/-- A second autonomous expansion supplies the rank tree. -/
def rank35 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family34 n + 42) (Autonomous.encode (schedule35 n)))

/-- W-ranked hyperreflection of operator-meta-language address ladders. -/
def F35 (n : Nat) : Nat :=
  wDiagonalLift (schedule35 n) (rank35 n) osTransformer (fun _ => family34) n n

/-- **Contender 35.** Never evaluate it. -/
def contender_35 : Nat := F35 (F35 42)

end BusyLean
