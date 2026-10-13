import BusyLean.SystemFT.Trees
import BusyLean.Contender34

/-!
# Contender 35: impredicative trees

```
contender_35 := F35 (F35 42)
F35 n        := wDiagonalLift (schedule35 n) (rank35 n) ftTransformer (fun _ => family34) n n
```

Every earlier tree was built by a predicative construction: collapsing
functions, universes of codes, or System T over trees and its stackings. Here
the trees come from **impredicative** programs. `SystemFT` is System F with a
base type `tree` and inert constructors `con 0 : tree`, `con 1 : tree -> tree`,
`con 2 : (nat -> tree) -> tree`. Reducibility candidates give every closed
program of type `tree` a well-founded tree (`FT.wt_of_typed`), and `FT.toTree`
reads it off by well-founded recursion. Through Church encodings, such programs
denote every tree that System F can describe.

At input `n` the tree `ftTree n` is the supremum of Contender 34's tree and the
trees of all System FT programs of depth `<= n` (oracle: Contender 34's
family). The ladder runs over its addresses, and the W-ranked lift hierarchy
is seeded with `family34 n = F34 (F34 n)`.

**Do not evaluate `contender_35`.**
-/

namespace BusyLean

/-- Contender 34's construction as a function of its input: `family34 42 = contender_34`. -/
def family34 (n : Nat) : Nat := F34 (F34 n)

/-- Contender 34's tree joined with the trees of all System FT programs of depth `<= n`. -/
def ftTree (n : Nat) : Ordinal.CTree := FT.progSup family34 (Ordinal.treeStackedTree n) n

end BusyLean

namespace BusyLean.FL

open Ordinal

theorem sn_erase_fttree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (ftTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (ftTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `ftTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def ftvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (ftTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_fttree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `ftTree n`. -/
def ftLadderUpTo (n : Nat) : List (CTm (Addr (ftTree n))) := ctmsUpTo (addrUpTo (ftTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectFTFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.ftvalue n (packFamily fs) n) (FL.ftLadderUpTo n))

def ftTransformer : Transformer := fun fs _ n => reflectFTFamily fs n

def schedule35 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family34 n + 42) (Autonomous.encode (schedule34 n)))

def rank35 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family34 n + 42) (Autonomous.encode (schedule35 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 34's family. -/
def F35 (n : Nat) : Nat :=
  wDiagonalLift (schedule35 n) (rank35 n) ftTransformer (fun _ => family34) n n

/-- **Contender 35.** Never evaluate it. -/
def contender_35 : Nat := F35 (F35 42)

end BusyLean
