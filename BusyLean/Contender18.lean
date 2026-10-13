import BusyLean.Ordinal.Veblen
import BusyLean.Contender17

/-!
# Contender 18: a ladder of universes of length `Γ₀`

```
contender_18 := F18 (F18 42)
F18 n        := diagonalLift (schedule18 n) (rank18 n) gTransformer (fun _ => family17) n n
```

Contender 17's ladder had length `ε₀`. Here the atoms are hereditarily sorted
binary Veblen terms (`Ordinal.Gamma0`), notations whose order type is at least
`Γ₀`. Their well-foundedness (`Ordinal.gamma0_wf`) follows Schütte's argument
using only the case split of the Boolean comparison. The universes are
`FL.wfUniv` and normalization is `FL.sn_of_typed`, as before.

At depth `n`, programs use Veblen terms of height `≤ n`, i.e. levels up to
`φ`-towers such as `φ(φ(…), 0)` of height about `n`. The amplifier is the rank
hierarchy of lifts, seeded with Contender 17's family `family17 n = F17 (F17 n)`.

**Do not evaluate `contender_18`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_gamma0 {f : Nat → Nat} {fuel : Nat} {t : CTm Gamma0}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f gamma0_wf) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a Γ₀-ladder program (type checked with `fuel`) relative
to the oracle `f`. -/
def gvalue (f : Nat → Nat) (fuel : Nat) (t : CTm Gamma0) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_gamma0 (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Γ₀-ladder programs of depth `≤ n`. -/
def gamma0LadderUpTo (n : Nat) : List (CTm Gamma0) := ctmsUpTo (gamma0UpTo n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Γ₀-ladder reflection with a countable oracle family. -/
def reflectGFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.gvalue (packFamily fs) n) (FL.gamma0LadderUpTo n))

def gTransformer : Transformer := fun fs _ n => reflectGFamily fs n

/-- Contender 17's construction as a function of its input: `family17 42 = contender_17`. -/
def family17 (n : Nat) : Nat := F17 (F17 n)

def schedule18 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family17 n + 42) (Autonomous.encode tree12))

def rank18 (n : Nat) : Nat := family17 n + 1

/-- Diagonal hyperreflection of the Γ₀-ladder, seeded with Contender 17's family. -/
def F18 (n : Nat) : Nat :=
  diagonalLift (schedule18 n) (rank18 n) gTransformer (fun _ => family17) n n

/-- **Contender 18.** Never evaluate it. -/
def contender_18 : Nat := F18 (F18 42)

end BusyLean
