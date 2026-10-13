import BusyLean.Ordinal.TreeUniverses2
import BusyLean.Contender27

/-!
# Contender 28: universes of level codes along tree ordinals

```
contender_28 := F28 (F28 42)
F28 n        := wDiagonalLift (schedule28 n) (rank28 n) rtTransformer (fun _ => family27) n n
```

Contender 27 stacked universes of level codes along the natural numbers. Here
universes are stacked along countable tree ordinals (`Ordinal.TreeUniverses2`).
Unions of universes are universes, so `univT` is defined by structural
recursion on a tree. The number of stacked universes is itself the previous
round's collapsed tree: `roundTree n` iterates `n+1` times
`Λ ↦ collapse in the universe after univT Λ`, starting from Contender 27's
tree. No axioms are used. Input `n` uses the ladder over the addresses of
`roundTree n`.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 27's
family `family27 n = F27 (F27 n)`.

**Do not evaluate `contender_28`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_rtree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (roundTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (roundTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `roundTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def rtvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (roundTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_rtree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `roundTree n`. -/
def rtreeLadderUpTo (n : Nat) : List (CTm (Addr (roundTree n))) := ctmsUpTo (addrUpTo (roundTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectRTFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.rtvalue n (packFamily fs) n) (FL.rtreeLadderUpTo n))

def rtTransformer : Transformer := fun fs _ n => reflectRTFamily fs n

/-- Contender 27's construction as a function of its input: `family27 42 = contender_27`. -/
def family27 (n : Nat) : Nat := F27 (F27 n)

def schedule28 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family27 n + 42) (Autonomous.encode (schedule27 n)))

def rank28 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family27 n + 42) (Autonomous.encode (schedule28 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 27's family. -/
def F28 (n : Nat) : Nat :=
  wDiagonalLift (schedule28 n) (rank28 n) rtTransformer (fun _ => family27) n n

/-- **Contender 28.** Never evaluate it. -/
def contender_28 : Nat := F28 (F28 42)

end BusyLean
