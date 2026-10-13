import BusyLean.Ordinal.Buchholz
import BusyLean.Contender20

/-!
# Contender 21: ladders of length `ψ₀(ε_{Ω_n+1})`, diagonalized up to `ψ₀(Ω_ω)`

```
contender_21 := F21 (F21 42)
F21 n        := diagonalLift (schedule21 n) (rank21 n) zTransformer (fun _ => family20) n n
```

Contender 20's ladder used two-level collapsing terms (the Bachmann–Howard
ordinal). Here the atoms at input `n` are Buchholz-style collapsing terms
with levels `0, …, n` (`Ordinal.Buchholz n`), whose normal forms reach
`ψ₀(ε_{Ω_n+1})`. Like Contender 14 with its finite ladders, the reflection
diagonalizes over the notation as well. Input `n` uses the level bound `n`,
so the lengths of the ladders climb to Buchholz's ordinal `ψ₀(Ω_ω)`.

`Ordinal.buchholz_wf n` proves each notation well-founded by downward
induction on the level, relativizing the impredicative argument of
Contender 20 to scopes. The universes are `FL.wfUniv` and normalization is
`FL.sn_of_typed`.

The amplifier is the rank hierarchy of lifts, seeded with Contender 20's
family `family20 n = F20 (F20 n)`.

**Do not evaluate `contender_21`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_buchholz {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Buchholz L)}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (buchholz_wf L)) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the level-`L` Buchholz atoms (type checked with
`fuel`) relative to the oracle `f`. -/
def zvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Buchholz L)) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_buchholz L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the level-`n` Buchholz atoms. -/
def buchholzLadderUpTo (n : Nat) : List (CTm (Buchholz n)) := ctmsUpTo (buchholzUpTo n n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Buchholz-ladder reflection with a countable oracle family; the input is
also the level bound. -/
def reflectZFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.zvalue n (packFamily fs) n) (FL.buchholzLadderUpTo n))

def zTransformer : Transformer := fun fs _ n => reflectZFamily fs n

/-- Contender 20's construction as a function of its input: `family20 42 = contender_20`. -/
def family20 (n : Nat) : Nat := F20 (F20 n)

def schedule21 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family20 n + 42) (Autonomous.encode tree12))

def rank21 (n : Nat) : Nat := family20 n + 1

/-- Diagonal hyperreflection of the Buchholz ladders, seeded with Contender 20's family. -/
def F21 (n : Nat) : Nat :=
  diagonalLift (schedule21 n) (rank21 n) zTransformer (fun _ => family20) n n

/-- **Contender 21.** Never evaluate it. -/
def contender_21 : Nat := F21 (F21 42)

end BusyLean
