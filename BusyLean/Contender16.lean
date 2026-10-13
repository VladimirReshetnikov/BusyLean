import BusyLean.Ordinal.OmegaPow
import BusyLean.Contender15

/-!
# Contender 16: a transfinite ladder of universes

```
contender_16 := F16 (F16 42)
F16 n        := diagonalLift (schedule16 n) (rank16 n) tTransformer (fun _ => family15) n n
```

Contender 14's ladder had one universe per natural number. Here the atoms are
notations for the ordinals below `ω^ω` (`Ordinal.OmegaPow`). The universe of
atom `a` holds the operators of every base kind built from atoms below `a`, so
the universe at `ω` holds operators from every finite level at once, the one at
`ω + 1` holds operators over it, and so on up to `ω^ω`.

* `FL.wfUniv` builds the universes by well-founded recursion over the atom
  order; `Ordinal.wf_sorted` proves that order well-founded. Normalization is
  the same parametric theorem `FL.sn_of_typed`.
* `reflectTFamily fs n` exceeds every visible coordinate `fs i n` and every
  program of depth `≤ n` whose atoms have `≤ n` terms with exponents `< n`
  (levels up to `ω^(n-1)·n`). The programs get the family as a packed oracle.
* The amplifier is the rank hierarchy of lifts of Contender 15, seeded with
  Contender 15's family `family15 n = F15 (F15 n)`.

**Do not evaluate `contender_16`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_omegaPow {f : Nat → Nat} {fuel : Nat} {t : CTm OmegaPow}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f omegaPow_wf) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a transfinite-ladder program (type checked with `fuel`) relative
to the oracle `f`. -/
def tvalue (f : Nat → Nat) (fuel : Nat) (t : CTm OmegaPow) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_omegaPow (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Transfinite-ladder programs of depth `≤ n`. -/
def transfiniteUpTo (n : Nat) : List (CTm OmegaPow) := ctmsUpTo (omegaPowUpTo n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Transfinite-ladder reflection with a countable oracle family. -/
def reflectTFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.tvalue (packFamily fs) n) (FL.transfiniteUpTo n))

def tTransformer : Transformer := fun fs _ n => reflectTFamily fs n

/-- Contender 15's construction as a function of its input: `family15 42 = contender_15`. -/
def family15 (n : Nat) : Nat := F15 (F15 n)

def schedule16 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family15 n + 42) (Autonomous.encode tree12))

def rank16 (n : Nat) : Nat := family15 n + 1

/-- Diagonal hyperreflection of the transfinite ladder, seeded with Contender 15's family. -/
def F16 (n : Nat) : Nat :=
  diagonalLift (schedule16 n) (rank16 n) tTransformer (fun _ => family15) n n

/-- **Contender 16.** Never evaluate it. -/
def contender_16 : Nat := F16 (F16 42)

end BusyLean
