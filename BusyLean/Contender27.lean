import BusyLean.Ordinal.TreeUniverses
import BusyLean.Contender26

/-!
# Contender 27: universes of level codes

```
contender_27 := F27 (F27 42)
F27 n        := wDiagonalLift (schedule27 n) (rank27 n) uTransformer (fun _ => family26) n n
```

Contender 26 indexed collapsing levels by countable codes. Here level codes
form stratified universes (`Ordinal.TreeUniverses`). The codes of universe
`k+1` have suprema ranging over the lower parts `Low c` of universe-`k` codes,
so they can denote levels as large as universe-`k` level elements. Each
universe has its own collapse `DN`, by structural recursion, and no axioms are
used. Input `n` uses the ladder over the addresses of `universeLadderTree n`,
the collapse of `ε_{Ω_top+1}` in universe `n+1`. Heuristically the nesting
`Ω_{Ω_{⋯}}` grows with `n`, toward the first fixed point of `α ↦ Ω_α`.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 26's
family `family26 n = F26 (F26 n)`.

**Do not evaluate `contender_27`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_utree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (universeLadderTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (universeLadderTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `universeLadderTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def uvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (universeLadderTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_utree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `universeLadderTree n`. -/
def utreeLadderUpTo (n : Nat) : List (CTm (Addr (universeLadderTree n))) := ctmsUpTo (addrUpTo (universeLadderTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectUFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.uvalue n (packFamily fs) n) (FL.utreeLadderUpTo n))

def uTransformer : Transformer := fun fs _ n => reflectUFamily fs n

/-- Contender 26's construction as a function of its input: `family26 42 = contender_26`. -/
def family26 (n : Nat) : Nat := F26 (F26 n)

def schedule27 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family26 n + 42) (Autonomous.encode (schedule26 n)))

def rank27 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family26 n + 42) (Autonomous.encode (schedule27 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 26's family. -/
def F27 (n : Nat) : Nat :=
  wDiagonalLift (schedule27 n) (rank27 n) uTransformer (fun _ => family26) n n

/-- **Contender 27.** Never evaluate it. -/
def contender_27 : Nat := F27 (F27 42)

end BusyLean
