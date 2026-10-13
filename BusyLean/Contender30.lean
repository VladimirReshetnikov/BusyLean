import BusyLean.Ordinal.TreeUniverses4
import BusyLean.Contender29

/-!
# Contender 30: closure functionals of all finite types

```
contender_30 := F30 (F30 42)
F30 n        := wDiagonalLift (schedule30 n) (rank30 n) tlTransformer (fun _ => family29) n n
```

Contender 29 took closure points of universe operators. Here closure is lifted
to all finite types over universes (`Ordinal.TreeUniverses4`): `A 0 = Univ` and
`A (k+1) = A k → A k`, with pointwise unions. `closureA k f` is the union of
`f`'s iterates. At input `n` the chain `closureA n, …, closureA 0` is applied to
Contender 29's operator `ΦT (operatorTree n)` and then to the base universe. The
resulting universe is collapsed to a countable tree, and the ladder runs over
its addresses. No axioms are used.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 29's
family `family29 n = F29 (F29 n)`.

**Do not evaluate `contender_30`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_tltree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (typeLevelTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (typeLevelTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `typeLevelTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def tlvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (typeLevelTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_tltree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `typeLevelTree n`. -/
def tltreeLadderUpTo (n : Nat) : List (CTm (Addr (typeLevelTree n))) := ctmsUpTo (addrUpTo (typeLevelTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectTLFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.tlvalue n (packFamily fs) n) (FL.tltreeLadderUpTo n))

def tlTransformer : Transformer := fun fs _ n => reflectTLFamily fs n

/-- Contender 29's construction as a function of its input: `family29 42 = contender_29`. -/
def family29 (n : Nat) : Nat := F29 (F29 n)

def schedule30 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family29 n + 42) (Autonomous.encode (schedule29 n)))

def rank30 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family29 n + 42) (Autonomous.encode (schedule30 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 29's family. -/
def F30 (n : Nat) : Nat :=
  wDiagonalLift (schedule30 n) (rank30 n) tlTransformer (fun _ => family29) n n

/-- **Contender 30.** Never evaluate it. -/
def contender_30 : Nat := F30 (F30 42)

end BusyLean
