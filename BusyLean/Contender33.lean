import BusyLean.Ordinal.TreeLanguage2
import BusyLean.Contender32

/-!
# Contender 33: languages stacked on languages

```
contender_33 := F33 (F33 42)
F33 n        := wDiagonalLift (schedule33 n) (rank33 n) skTransformer (fun _ => family32) n n
```

Contender 32 took all closed tree programs of bounded size over a primitive
`boost`. Here the whole language becomes the next primitive
(`Ordinal.TreeLanguage2`). `langLift b t` is every closed `tree ⇒ tree` program
over `b`, of every size, applied to `t`. Then `boostK (k+1) = langLift (boostK k)`,
starting from Contender 31's construction. `stackedTree n` applies `boostK (n+1)`
to Contender 32's tree, and input `n` uses the ladder over its addresses.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 32's
family `family32 n = F32 (F32 n)`.

**Do not evaluate `contender_33`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_sktree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (stackedTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (stackedTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `stackedTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def skvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (stackedTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_sktree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `stackedTree n`. -/
def sktreeLadderUpTo (n : Nat) : List (CTm (Addr (stackedTree n))) := ctmsUpTo (addrUpTo (stackedTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectSKFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.skvalue n (packFamily fs) n) (FL.sktreeLadderUpTo n))

def skTransformer : Transformer := fun fs _ n => reflectSKFamily fs n

/-- Contender 32's construction as a function of its input: `family32 42 = contender_32`. -/
def family32 (n : Nat) : Nat := F32 (F32 n)

def schedule33 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family32 n + 42) (Autonomous.encode (schedule32 n)))

def rank33 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family32 n + 42) (Autonomous.encode (schedule33 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 32's family. -/
def F33 (n : Nat) : Nat :=
  wDiagonalLift (schedule33 n) (rank33 n) skTransformer (fun _ => family32) n n

/-- **Contender 33.** Never evaluate it. -/
def contender_33 : Nat := F33 (F33 42)

end BusyLean
