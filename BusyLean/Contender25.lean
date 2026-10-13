import BusyLean.Ordinal.TreeCollapse
import BusyLean.Contender24

/-!
# Contender 25: ladders over addresses in collapsed tree ordinals

```
contender_25 := F25 (F25 42)
F25 n        := wDiagonalLift (schedule25 n) (rank25 n) aTransformer (fun _ => family24) n n
```

Proposal P25's idea, generalized. The atoms are finite addresses in a
Lean-defined tree ordinal, ordered by strict descent. The order is
well-founded by structural recursion on the tree (`Ordinal.addr_wf`), whatever
ordinal the tree denotes, so the ladder length is just the rank of the tree. No
ordinal-notation proof is needed.

The tree at input `n` is `Ordinal.bigTree n = D 0 (ε-numbers above Ω_ω + 1)`.
`D` is a family of Buchholz-style collapsing functions on tree ordinals, for
all finite levels at once, defined by structural recursion. Heuristically the
rank is `ψ₀(ε_{Ω_ω+n})`, beyond Buchholz's ordinal `ψ₀(Ω_ω)` and beyond the
towers of Contenders 22–24. This is exactly the range where a proof by
ordinal notations would need distinguished sets.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 24's
family `family24 n = F24 (F24 n)`.

**Do not evaluate `contender_25`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_addr {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (bigTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (bigTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `bigTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def avalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (bigTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_addr L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `bigTree n`. -/
def addrLadderUpTo (n : Nat) : List (CTm (Addr (bigTree n))) := ctmsUpTo (addrUpTo (bigTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectAFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.avalue n (packFamily fs) n) (FL.addrLadderUpTo n))

def aTransformer : Transformer := fun fs _ n => reflectAFamily fs n

/-- Contender 24's construction as a function of its input: `family24 42 = contender_24`. -/
def family24 (n : Nat) : Nat := F24 (F24 n)

def schedule25 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family24 n + 42) (Autonomous.encode (schedule24 n)))

def rank25 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family24 n + 42) (Autonomous.encode (schedule25 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 24's family. -/
def F25 (n : Nat) : Nat :=
  wDiagonalLift (schedule25 n) (rank25 n) aTransformer (fun _ => family24) n n

/-- **Contender 25.** Never evaluate it. -/
def contender_25 : Nat := F25 (F25 42)

end BusyLean
