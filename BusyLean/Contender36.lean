import BusyLean.SystemFLT.Trees
import BusyLean.Contender35

/-!
# Contender 36: ladders that build their own length

```
contender_36 := F36 (F36 42)
F36 n        := wDiagonalLift (schedule36 n) (rank36 n) btTransformer (fun _ => family35) n n
```

Contender 35 took its trees from System F programs. Here the trees come from
the **ladder language itself**. `SystemFLT` is the ladder language over the
terms of System FT. A ladder program over the addresses of a tree `t` with the
Church tree type `FLT.treeTy`, applied to the inert constructors, denotes a
well-founded tree (`FLT.wt_of_treeTy`). One bootstrap step

  `ladderTree t = lim (t, trees of all ladder programs of depth <= n over Addr t)`

turns the ladder over `t` into a longer tree. `bootT` iterates it along a tree
index, with limits at limit nodes. At input `n` both the index and the start
are Contender 35's tree `ftTree n`, and the final ladder runs over the addresses
of the result.

**Do not evaluate `contender_36`.**
-/

namespace BusyLean.FLT

open BusyLean.FL (Kind Ty kindsUpTo tysUpTo)
open BusyLean.Ordinal

variable {α : Type}

/-- Church-style ladder programs of enumeration depth `<= n` over the atoms `as`. -/
def ctmsUpTo (as : List α) : Nat → List (CTm α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      let ts := tysUpTo as n
      let es := ctmsUpTo as n
      (BigNumber.natsUpTo n).map CTm.var ++
      ((BigNumber.cross ts es).map (fun p => CTm.lam p.1 p.2) ++
      ((BigNumber.cross es es).map (fun p => CTm.app p.1 p.2) ++
      ((BigNumber.cross ks es).map (fun p => CTm.tlam p.1 p.2) ++
      ((BigNumber.cross es ts).map (fun p => CTm.tapp p.1 p.2) ++
      (es.map CTm.klam0 ++
      ((BigNumber.cross es ks).map (fun p => CTm.kapp0 p.1 p.2) ++
      (es.map CTm.klam1 ++
      ((BigNumber.cross es ks).map (fun p => CTm.kapp1 p.1 p.2) ++
      [CTm.orc]))))))))

/-- The tree of a ladder program over the addresses of `t` (type checked with `fuel`),
relative to the oracle `f`: defined when the program has the Church tree type. -/
def progTree (f : Nat → Nat) (t : CTree) (fuel : Nat) (p : CTm (Addr t)) : CTree :=
  match h : infer fuel [] [] p with
  | some A =>
      if hA : A = treeTy then
        FT.toTree f ⟨applyCons (erase p), wt_of_treeTy (wfUniv f (addr_wf t))
          (infer_sound fuel p (goodCtx_nil []) (h.trans (congrArg some hA))).1⟩
      else .zero
  | none => .zero

/-- One bootstrap step: `t` joined with the trees of all ladder programs of depth `<= n`
over the addresses of `t`. -/
def ladderTree (f : Nat → Nat) (n : Nat) (t : CTree) : CTree :=
  .lim fun i =>
    if i = 0 then t else ((ctmsUpTo (addrUpTo t n) n).map (progTree f t n)).getD (i - 1) .zero

/-- Bootstrap steps iterated along a tree index, starting from `base`. -/
def bootT (f : Nat → Nat) (n : Nat) (base : CTree) : CTree → CTree
  | .zero => base
  | .succ c => ladderTree f n (bootT f n base c)
  | .lim g => .lim fun i => bootT f n base (g i)
  | .supL _ => base
  | .supH _ => base

end BusyLean.FLT

namespace BusyLean

/-- Contender 35's construction as a function of its input: `family35 42 = contender_35`. -/
def family35 (n : Nat) : Nat := F35 (F35 n)

/-- Contender 35's tree, bootstrapped along itself by ladder programs. -/
def bootTree (n : Nat) : Ordinal.CTree := FLT.bootT family35 n (ftTree n) (ftTree n)

end BusyLean

namespace BusyLean.FL

open Ordinal

theorem sn_erase_boottree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (bootTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (bootTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `bootTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def btvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (bootTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_boottree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `bootTree n`. -/
def btLadderUpTo (n : Nat) : List (CTm (Addr (bootTree n))) := ctmsUpTo (addrUpTo (bootTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectBTFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.btvalue n (packFamily fs) n) (FL.btLadderUpTo n))

def btTransformer : Transformer := fun fs _ n => reflectBTFamily fs n

def schedule36 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family35 n + 42) (Autonomous.encode (schedule35 n)))

def rank36 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family35 n + 42) (Autonomous.encode (schedule36 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 35's family. -/
def F36 (n : Nat) : Nat :=
  wDiagonalLift (schedule36 n) (rank36 n) btTransformer (fun _ => family35) n n

/-- **Contender 36.** Never evaluate it. -/
def contender_36 : Nat := F36 (F36 42)

end BusyLean
