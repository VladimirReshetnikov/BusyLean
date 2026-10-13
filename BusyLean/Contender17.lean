import BusyLean.Ordinal.Epsilon0
import BusyLean.Contender16

/-!
# Contender 17: a ladder of universes of length `ε₀`

```
contender_17 := F17 (F17 42)
F17 n        := diagonalLift (schedule17 n) (rank17 n) eTransformer (fun _ => family16) n n
```

Contender 16's ladder had length `ω^ω`. Here the atoms are Cantor normal form
trees, notations for the ordinals below `ε₀` (`Ordinal.Epsilon0`). Their
well-foundedness (`Ordinal.epsilon0_wf`) applies the sorted-list lemma
hereditarily. The universes are again `FL.wfUniv`, and normalization is
`FL.sn_of_typed`.

At depth `n`, programs use atoms of height `≤ n` with `≤ n` terms per node, i.e.
levels up to towers `ω^ω^⋯` of height about `n`. The amplifier is the rank
hierarchy of lifts, seeded with Contender 16's family `family16 n = F16 (F16 n)`.

**Do not evaluate `contender_17`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_epsilon0 {f : Nat → Nat} {fuel : Nat} {t : CTm Epsilon0}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f epsilon0_wf) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of an ε₀-ladder program (type checked with `fuel`) relative
to the oracle `f`. -/
def evalue (f : Nat → Nat) (fuel : Nat) (t : CTm Epsilon0) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_epsilon0 (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- ε₀-ladder programs of depth `≤ n`. -/
def epsilon0LadderUpTo (n : Nat) : List (CTm Epsilon0) := ctmsUpTo (epsilon0UpTo n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- ε₀-ladder reflection with a countable oracle family. -/
def reflectEFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.evalue (packFamily fs) n) (FL.epsilon0LadderUpTo n))

def eTransformer : Transformer := fun fs _ n => reflectEFamily fs n

/-- Contender 16's construction as a function of its input: `family16 42 = contender_16`. -/
def family16 (n : Nat) : Nat := F16 (F16 n)

def schedule17 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family16 n + 42) (Autonomous.encode tree12))

def rank17 (n : Nat) : Nat := family16 n + 1

/-- Diagonal hyperreflection of the ε₀-ladder, seeded with Contender 16's family. -/
def F17 (n : Nat) : Nat :=
  diagonalLift (schedule17 n) (rank17 n) eTransformer (fun _ => family16) n n

/-- **Contender 17.** Never evaluate it. -/
def contender_17 : Nat := F17 (F17 42)

end BusyLean
