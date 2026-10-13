import BusyLean.Ordinal.BuchholzBase
import BusyLean.Contender21

/-!
# Contender 22: ladders over a tower of relativized Buchholz notations

```
contender_22 := F22 (F22 42)
F22 n        := diagonalLift (schedule22 n) (rank22 n) twTransformer (fun _ => family21) n n
```

Contender 21 diagonalized over the level-bounded Buchholz notations, up to
`ψ₀(Ω_ω)`. Here the atoms at input `n` come from `Ordinal.tower n`. `tower 1` is
the union of all level-bounded systems (order type `ψ₀(Ω_ω)`, well-founded
because the bound is compared first). Each further step takes the union of all
level-bounded systems *over the previous step as base atoms*. Atoms lie below
every collapse, but may occur inside collapse arguments, so each round
collapses over everything below it. Heuristically `tower k` has order type
about `ψ₀(Ω_ω · k)`, and the diagonal goes beyond `ψ₀(Ω_ω)`.

The well-foundedness of every step is `BuchB.stepR`: the level step of
Contender 21, with base atoms accessible from the base's own well-foundedness.

The amplifier is the rank hierarchy of lifts, seeded with Contender 21's
family `family21 n = F21 (F21 n)`.

**Do not evaluate `contender_22`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_tower {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (tower L).T}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (tower_wf L)) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the atoms of `tower L` (type checked with
`fuel`) relative to the oracle `f`. -/
def tvalue22 (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (tower L).T) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_tower L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the atoms of `tower n`. -/
def towerLadderUpTo (n : Nat) : List (CTm (tower n).T) := ctmsUpTo ((tower n).enum n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Tower-ladder reflection with a countable oracle family; the input is
also the tower height. -/
def reflectTwFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.tvalue22 n (packFamily fs) n) (FL.towerLadderUpTo n))

def twTransformer : Transformer := fun fs _ n => reflectTwFamily fs n

/-- Contender 21's construction as a function of its input: `family21 42 = contender_21`. -/
def family21 (n : Nat) : Nat := F21 (F21 n)

def schedule22 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family21 n + 42) (Autonomous.encode tree12))

def rank22 (n : Nat) : Nat := family21 n + 1

/-- Diagonal hyperreflection of the tower ladders, seeded with Contender 21's family. -/
def F22 (n : Nat) : Nat :=
  diagonalLift (schedule22 n) (rank22 n) twTransformer (fun _ => family21) n n

/-- **Contender 22.** Never evaluate it. -/
def contender_22 : Nat := F22 (F22 42)

end BusyLean
