import BusyLean.Ordinal.WTreeLadder
import BusyLean.Contender19

/-!
# Contender 20: autonomous W-tree universe reflection

```
contender_20 := F20 (F20 42)
F20 n        := diagonalLift (schedule20 n) (rank20 n)
                  aTransformer orbit19 n n
```

Contender 19 uses a linearly ordered ladder of explicit large-Veblen
notations.  Here the atoms are valid finite addresses in
`Ordinal.autonomousUniverseTree`, a countably branching well-founded tree that
contains the W-language-generated `tree12` and every finite autonomous
hyper-closure above it.  The resulting object language is a ramified tree of
predicative universes.  Its strong normalization is an immediate instance of
`FL.sn_of_typed` over the generic well-founded universe `FL.wfUniv`.

The seed family exposes the finite orbit of `F19`: coordinate `i` contains the
`(i+2)`-fold iterate of `F19`.  In particular coordinate zero is exactly
Contender 19's family.  The schedule and diagonal rank are then self-fed from
an orbit whose length is itself `family19 n`.

All recursion is structural.  The definition is computable in principle, but
it must never be evaluated at the contest input.
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_wlevel {f : Nat → Nat} {fuel : Nat} {t : CTm WLevel}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f wLevel_wf) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a ramified W-tree-universe program, type checked with `fuel`,
relative to the oracle `f`. -/
def avalue (f : Nat → Nat) (fuel : Nat) (t : CTm WLevel) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_wlevel (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Ramified W-tree-universe programs of depth `≤ n`. -/
def autonomousLadderUpTo (n : Nat) : List (CTm WLevel) :=
  ctmsUpTo (wLevelsUpTo n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Reflection over the ramified W-tree universe hierarchy, with a countable
oracle family. -/
def reflectAFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.avalue (packFamily fs) n)
      (FL.autonomousLadderUpTo n))

/-- The family-aware ramified-universe reflection transformer. -/
def aTransformer : Transformer := fun fs _ n => reflectAFamily fs n

/-- Contender 19's construction as a function of its input:
`family19 42 = contender_19`. -/
def family19 (n : Nat) : Nat := F19 (F19 n)

/-- Finite iteration of `F19`, with the next iterate exposed at the outermost
constructor.  This orientation makes strict growth use only `input_lt_F19`;
no monotonicity of reflection is assumed. -/
def iterateF19 : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => F19 (iterateF19 k n)

/-- Coordinate `i` is the `(i+2)`-fold finite orbit of `F19` from `n`.
Coordinate zero is definitionally `family19 n`. -/
def orbit19 : Family := fun i n => iterateF19 (i + 2) n

/-- A self-fed orbit value used for the schedule and the lift rank. -/
def seedHeight20 (n : Nat) : Nat := orbit19 (family19 n) n

/-- The autonomous schedule is now built above the same W-tree that indexes the
object language, at a self-fed hyper level. -/
def schedule20 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (seedHeight20 n + 42)
      (Autonomous.encode Ordinal.autonomousUniverseTree))

/-- Self-fed rank for diagonal hyperreflection. -/
def rank20 (n : Nat) : Nat := seedHeight20 n + 1

/-- Diagonal hyperreflection of the ramified W-tree universe language. -/
def F20 (n : Nat) : Nat :=
  diagonalLift (schedule20 n) (rank20 n)
    aTransformer orbit19 n n

/-- **Contender 20.** Never evaluate it. -/
def contender_20 : Nat := F20 (F20 42)

end BusyLean
