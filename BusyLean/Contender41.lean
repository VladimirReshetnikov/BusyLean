import BusyLean.SystemFLT2.Trees
import BusyLean.Contender40

/-!
# Contender 41: the ladder jump that reads its input

```
contender_41 := F41 (F41 42)
F41 n        := hier family40 (readerTree (family40 n)) (family40 n)
```

System FT2 gave System F a recursor over an input tree. `SystemFLT2` gives the
same to the ladder language (dynamic kinds, a universe per named atom). A
ladder program of the reader type `FLT2.readerTy` receives the constructors, a
recursor, and the input tree, and denotes a well-founded tree
(`FLT2.wt_of_readerTy`). `jumpL g n T` joins `T` with the trees of all reader
programs of depth `<= n` over the addresses of `T`, with `T` as the oracle
tree. This jump reads its input with the full strength of the ladder.

The base transformer joins `jumpL` with Contender 40's base. P27's
metalanguages over it are stacked to the height of Contender 40's tree, and the
number is read off with `hier`.

**Do not evaluate `contender_41`.**
-/

namespace BusyLean.FLT2

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

/-- The tree a reader program over the addresses of `T` builds from `T` (type
checked with `fuel`); `zero` unless it has the reader type. -/
def readTree (g : Nat → Nat) (T : CTree) (fuel : Nat) (p : CTm (Addr T)) : CTree :=
  match h : infer fuel [] [] p with
  | some A =>
      if hA : A = readerTy then
        FT2.toTree ⟨g, T⟩ ⟨applyReader (erase p), wt_of_readerTy (wfUniv ⟨g, T⟩ (addr_wf T))
          (infer_sound fuel p (goodCtx_nil []) (h.trans (congrArg some hA))).1⟩
      else .zero
  | none => .zero

/-- **The ladder jump.** `T` joined with the trees that all reader programs of depth
`<= n` over the addresses of `T` build from `T`. -/
def jumpL (g : Nat → Nat) (n : Nat) (T : CTree) : CTree :=
  .lim fun i =>
    if i = 0 then T else ((ctmsUpTo (addrUpTo T n) n).map (readTree g T n)).getD (i - 1) .zero

end BusyLean.FLT2

namespace BusyLean

/-- Contender 40's construction as a function of its input: `family40 42 = contender_40`. -/
def family40 (n : Nat) : Nat := F40 (F40 n)

/-- The base transformer: the ladder jump joined with Contender 40's base. -/
def base41 (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i => if i = 0 then FLT2.jumpL family40 N t else base40 N t

/-- Contender 40's tree, closed under metalanguages over `base41` stacked to its own height. -/
def readerTree (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then metaTree N
    else Ordinal.metaBoostT (metaTree N) (base41 N) (metaTree N)

/-- The hierarchy along the tree, based on Contender 40's family. -/
def F41 (n : Nat) : Nat := Ordinal.hier family40 (readerTree (family40 n)) (family40 n)

/-- **Contender 41.** Never evaluate it. -/
def contender_41 : Nat := F41 (F41 42)

end BusyLean
