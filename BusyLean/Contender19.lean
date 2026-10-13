import BusyLean.Ordinal.LargeVeblen
import BusyLean.Contender18

/-!
# Contender 19: a ladder of universes of large-Veblen length

```
contender_19 := F19 (F19 42)
F19 n        := diagonalLift (schedule19 n) (rank19 n) lTransformer (fun _ => family18) n n
```

Contender 18's ladder had length `Γ₀`. Here the atoms are Schütte's
Klammersymbole (`Ordinal.LargeVeblen`): `φ` applied to argument arrays whose
*positions are themselves terms*. Their normal forms reach the large Veblen
ordinal. Well-foundedness (`Ordinal.largeVeblen_wf`) again follows only the
case split of the Boolean comparison, now with argument arrays handled by the
predicate-restricted sorted-list lemma (`Ordinal.accQ_sorted`). The universes
are `FL.wfUniv` and normalization is `FL.sn_of_typed`.

The amplifier is the rank hierarchy of lifts, seeded with Contender 18's
family `family18 n = F18 (F18 n)`.

**Do not evaluate `contender_19`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_lveblen {f : Nat → Nat} {fuel : Nat} {t : CTm LargeVeblen}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f largeVeblen_wf) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a Veblen-ladder program (type checked with `fuel`) relative
to the oracle `f`. -/
def lvalue (f : Nat → Nat) (fuel : Nat) (t : CTm LargeVeblen) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_lveblen (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Veblen-ladder programs of depth `≤ n`. -/
def lveblenLadderUpTo (n : Nat) : List (CTm LargeVeblen) := ctmsUpTo (largeVeblenUpTo n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Veblen-ladder reflection with a countable oracle family. -/
def reflectLFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.lvalue (packFamily fs) n) (FL.lveblenLadderUpTo n))

def lTransformer : Transformer := fun fs _ n => reflectLFamily fs n

/-- Contender 18's construction as a function of its input: `family18 42 = contender_18`. -/
def family18 (n : Nat) : Nat := F18 (F18 n)

def schedule19 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family18 n + 42) (Autonomous.encode tree12))

def rank19 (n : Nat) : Nat := family18 n + 1

/-- Diagonal hyperreflection of the Veblen-ladder, seeded with Contender 18's family. -/
def F19 (n : Nat) : Nat :=
  diagonalLift (schedule19 n) (rank19 n) lTransformer (fun _ => family18) n n

/-- **Contender 19.** Never evaluate it. -/
def contender_19 : Nat := F19 (F19 42)

end BusyLean
