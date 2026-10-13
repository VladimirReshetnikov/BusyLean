import BusyLean.Ordinal.TreeUniverses3
import BusyLean.Contender28

/-!
# Contender 29: higher-order universe operators

```
contender_29 := F29 (F29 42)
F29 n        := wDiagonalLift (schedule29 n) (rank29 n) otTransformer (fun _ => family28) n n
```

Contender 28 built universes of level codes with `next` and `union`. Here the
universe-building operators are themselves iterated
(`Ordinal.TreeUniverses3`). `Φ F U` is the closure point of `F` above `U`, so
`Φ next` jumps to the next inaccessible-like universe. Operators are indexed by
tree ordinals: `ΦT 0 = next`, `ΦT (a+1) = Φ (ΦT a)`, and limits are unions.
`operatorTree n` iterates `n+1` rounds of
`Λ ↦ collapse in the universe after ΦT Λ base`, starting from Contender 28's
tree. No axioms are used. Input `n` uses the ladder over the addresses of
`operatorTree n`.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 28's
family `family28 n = F28 (F28 n)`.

**Do not evaluate `contender_29`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_otree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (operatorTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (operatorTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `operatorTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def otvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (operatorTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_otree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `operatorTree n`. -/
def otreeLadderUpTo (n : Nat) : List (CTm (Addr (operatorTree n))) := ctmsUpTo (addrUpTo (operatorTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectOTFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.otvalue n (packFamily fs) n) (FL.otreeLadderUpTo n))

def otTransformer : Transformer := fun fs _ n => reflectOTFamily fs n

/-- Contender 28's construction as a function of its input: `family28 42 = contender_28`. -/
def family28 (n : Nat) : Nat := F28 (F28 n)

def schedule29 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family28 n + 42) (Autonomous.encode (schedule28 n)))

def rank29 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family28 n + 42) (Autonomous.encode (schedule29 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 28's family. -/
def F29 (n : Nat) : Nat :=
  wDiagonalLift (schedule29 n) (rank29 n) otTransformer (fun _ => family28) n n

/-- **Contender 29.** Never evaluate it. -/
def contender_29 : Nat := F29 (F29 42)

end BusyLean
