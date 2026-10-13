import BusyLean.Ordinal.TowerAlong
import BusyLean.Contender23

/-!
# Contender 24: ladders over transfinite towers, indexed by the previous round

```
contender_24 := F24 (F24 42)
F24 n        := wDiagonalLift (schedule24 n) (rank24 n) rTransformer (fun _ => family23) n n
```

Contender 22's tower iterated relativized Buchholz systems along the natural
numbers. `Ordinal.TowerAlong` iterates along any well-founded index `J`. The
stage at `j` is built over the union of all stages below `j`, and the union of
all stages is again a well-founded order. So it indexes the next round:
`roundTower 0 = tower 1` and `roundTower (k+1) = limitAlong (roundTower k)`.
Heuristically the stage at `j` has order type `ψ₀(Ω_ω · (j+1))`, so the rounds
climb the fixed points of `x ↦ ψ₀(Ω_ω · x)`.

Input `n` uses the ladder over `roundTower n`. The amplifier is Contender 23's
W-ranked lift hierarchy, seeded with Contender 23's family
`family23 n = F23 (F23 n)`.

**Do not evaluate `contender_24`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_round {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (roundTower L).T}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (roundTower_wf L)) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the atoms of `roundTower L` (type checked with
`fuel`) relative to the oracle `f`. -/
def rvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (roundTower L).T) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_round L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the atoms of `roundTower n`. -/
def roundLadderUpTo (n : Nat) : List (CTm (roundTower n).T) := ctmsUpTo ((roundTower n).enum n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Round-tower reflection with a countable oracle family; the input is also the round. -/
def reflectRFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.rvalue n (packFamily fs) n) (FL.roundLadderUpTo n))

def rTransformer : Transformer := fun fs _ n => reflectRFamily fs n

/-- Contender 23's construction as a function of its input: `family23 42 = contender_23`. -/
def family23 (n : Nat) : Nat := F23 (F23 n)

def schedule24 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family23 n + 42) (Autonomous.encode (schedule23 n)))

def rank24 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family23 n + 42) (Autonomous.encode (schedule24 n)))

/-- W-ranked hyperreflection of the round-tower ladders, seeded with Contender 23's family. -/
def F24 (n : Nat) : Nat :=
  wDiagonalLift (schedule24 n) (rank24 n) rTransformer (fun _ => family23) n n

/-- **Contender 24.** Never evaluate it. -/
def contender_24 : Nat := F24 (F24 42)

end BusyLean
