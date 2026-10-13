import BusyLean.Ordinal.TreeUniverses5
import BusyLean.Contender30

/-!
# Contender 31: closure functionals of transfinite type

```
contender_31 := F31 (F31 42)
F31 n        := wDiagonalLift (schedule31 n) (rank31 n) ttTransformer (fun _ => family30) n n
```

Contender 30 took closure points at all finite types over universes. Here the
types are indexed by countable tree ordinals (`Ordinal.TreeUniverses5`):
`AT (a+1) = AT a → AT a` and `AT (lim f) = Π i, AT (f i)`. Canonical
functionals (`step`) are evaluated down to a universe along the canonical
chain. The type level at input `n` is Contender 30's tree `typeLevelTree n`.
The resulting universe is collapsed to a countable tree, and the ladder runs
over its addresses. No axioms are used.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 30's
family `family30 n = F30 (F30 n)`.

**Do not evaluate `contender_31`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_tttree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (transTypeTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (transTypeTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `transTypeTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def ttvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (transTypeTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_tttree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `transTypeTree n`. -/
def tttreeLadderUpTo (n : Nat) : List (CTm (Addr (transTypeTree n))) := ctmsUpTo (addrUpTo (transTypeTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectTTFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.ttvalue n (packFamily fs) n) (FL.tttreeLadderUpTo n))

def ttTransformer : Transformer := fun fs _ n => reflectTTFamily fs n

/-- Contender 30's construction as a function of its input: `family30 42 = contender_30`. -/
def family30 (n : Nat) : Nat := F30 (F30 n)

def schedule31 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family30 n + 42) (Autonomous.encode (schedule30 n)))

def rank31 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family30 n + 42) (Autonomous.encode (schedule31 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 30's family. -/
def F31 (n : Nat) : Nat :=
  wDiagonalLift (schedule31 n) (rank31 n) ttTransformer (fun _ => family30) n n

/-- **Contender 31.** Never evaluate it. -/
def contender_31 : Nat := F31 (F31 42)

end BusyLean
