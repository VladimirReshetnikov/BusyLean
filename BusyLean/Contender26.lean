import BusyLean.Ordinal.TreeLevels
import BusyLean.Contender25

/-!
# Contender 26: transfinitely many collapsing levels

```
contender_26 := F26 (F26 42)
F26 n        := wDiagonalLift (schedule26 n) (rank26 n) ltTransformer (fun _ => family25) n n
```

Contender 25's ladder ran over addresses in `bigTree n`, which collapses with
finitely many levels. Here the collapsing levels are themselves countable tree
ordinals (`Ordinal.TreeLevels`). `Low a` lumps all levels below `a`. Arguments
carry the level of every supremum (`supAt c g`). `DL a` collapses by
structural recursion, pattern-matching on the shape of the level: a successor
level diagonalizes through `DL c'`, and a limit level takes the limit of the
successor cases.

`ladderTree n` iterates `Λ ↦ DL 0 (ε_{Ω_Λ+1})` `n+1` times, starting from
`bigTree n`. Heuristically this climbs toward the fixed points of
`α ↦ ψ₀(Ω_α)`. The addresses are again well-founded structurally
(`Ordinal.addr_wf`).

The amplifier is the W-ranked lift hierarchy, seeded with Contender 25's
family `family25 n = F25 (F25 n)`.

**Do not evaluate `contender_26`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_ltree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (ladderTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (ladderTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `ladderTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def lvalue26 (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (ladderTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_ltree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `ladderTree n`. -/
def ltreeLadderUpTo (n : Nat) : List (CTm (Addr (ladderTree n))) := ctmsUpTo (addrUpTo (ladderTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectLTFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.lvalue26 n (packFamily fs) n) (FL.ltreeLadderUpTo n))

def ltTransformer : Transformer := fun fs _ n => reflectLTFamily fs n

/-- Contender 25's construction as a function of its input: `family25 42 = contender_25`. -/
def family25 (n : Nat) : Nat := F25 (F25 n)

def schedule26 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family25 n + 42) (Autonomous.encode (schedule25 n)))

def rank26 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family25 n + 42) (Autonomous.encode (schedule26 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 25's family. -/
def F26 (n : Nat) : Nat :=
  wDiagonalLift (schedule26 n) (rank26 n) ltTransformer (fun _ => family25) n n

/-- **Contender 26.** Never evaluate it. -/
def contender_26 : Nat := F26 (F26 42)

end BusyLean
