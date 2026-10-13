import BusyLean.Ordinal.BachmannHoward
import BusyLean.Contender19

/-!
# Contender 20: a ladder of universes of Bachmann–Howard length

```
contender_20 := F20 (F20 42)
F20 n        := diagonalLift (schedule20 n) (rank20 n) bTransformer (fun _ => family19) n n
```

Contender 19's ladder had large-Veblen length. Here the atoms are Buchholz-style
collapsing terms with two levels (`Ordinal.BachmannHoward`), whose normal forms
reach the Bachmann–Howard ordinal `ψ₀(ε_{Ω+1})`. Their well-foundedness
(`Ordinal.bachmannHoward_wf`) is the classical impredicative argument: the
order restricted to terms with accessible `D₀` components is well-founded, and
induction along it makes every `D₀ a` accessible. The universes are
`FL.wfUniv` and normalization is `FL.sn_of_typed`.

The amplifier is the rank hierarchy of lifts, seeded with Contender 19's
family `family19 n = F19 (F19 n)`.

**Do not evaluate `contender_20`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_bh {f : Nat → Nat} {fuel : Nat} {t : CTm BachmannHoward}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f bachmannHoward_wf) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a Bachmann–Howard-ladder program (type checked with `fuel`) relative
to the oracle `f`. -/
def bvalue (f : Nat → Nat) (fuel : Nat) (t : CTm BachmannHoward) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_bh (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Bachmann–Howard-ladder programs of depth `≤ n`. -/
def bhLadderUpTo (n : Nat) : List (CTm BachmannHoward) := ctmsUpTo (bachmannHowardUpTo n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Bachmann–Howard-ladder reflection with a countable oracle family. -/
def reflectBFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.bvalue (packFamily fs) n) (FL.bhLadderUpTo n))

def bTransformer : Transformer := fun fs _ n => reflectBFamily fs n

/-- Contender 19's construction as a function of its input: `family19 42 = contender_19`. -/
def family19 (n : Nat) : Nat := F19 (F19 n)

def schedule20 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family19 n + 42) (Autonomous.encode tree12))

def rank20 (n : Nat) : Nat := family19 n + 1

/-- Diagonal hyperreflection of the Bachmann–Howard-ladder, seeded with Contender 19's family. -/
def F20 (n : Nat) : Nat :=
  diagonalLift (schedule20 n) (rank20 n) bTransformer (fun _ => family19) n n

/-- **Contender 20.** Never evaluate it. -/
def contender_20 : Nat := F20 (F20 42)

end BusyLean
