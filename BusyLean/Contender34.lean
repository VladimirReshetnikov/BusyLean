import BusyLean.Ordinal.TreeLanguage3
import BusyLean.Contender33

/-!
# Contender 34: languages stacked along tree ordinals

```
contender_34 := F34 (F34 42)
F34 n        := wDiagonalLift (schedule34 n) (rank34 n) tsTransformer (fun _ => family33) n n
```

Contender 33 stacked the tree-ordinal language `n+1` times. Here the stacking
height is a tree ordinal (`Ordinal.TreeLanguage3`): `boostT (a+1) =
langLift (boostT a)`, with pointwise limits. At input `n`, both the height and
the argument are Contender 33's tree, and the ladder runs over the addresses of
the result.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 33's
family `family33 n = F33 (F33 n)`.

**Do not evaluate `contender_34`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_tstree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (treeStackedTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (treeStackedTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `treeStackedTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def tsvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (treeStackedTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_tstree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `treeStackedTree n`. -/
def tstreeLadderUpTo (n : Nat) : List (CTm (Addr (treeStackedTree n))) := ctmsUpTo (addrUpTo (treeStackedTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectTSFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.tsvalue n (packFamily fs) n) (FL.tstreeLadderUpTo n))

def tsTransformer : Transformer := fun fs _ n => reflectTSFamily fs n

/-- Contender 33's construction as a function of its input: `family33 42 = contender_33`. -/
def family33 (n : Nat) : Nat := F33 (F33 n)

def schedule34 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family33 n + 42) (Autonomous.encode (schedule33 n)))

def rank34 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family33 n + 42) (Autonomous.encode (schedule34 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 33's family. -/
def F34 (n : Nat) : Nat :=
  wDiagonalLift (schedule34 n) (rank34 n) tsTransformer (fun _ => family33) n n

/-- **Contender 34.** Never evaluate it. -/
def contender_34 : Nat := F34 (F34 42)

end BusyLean
