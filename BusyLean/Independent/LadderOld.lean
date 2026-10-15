import BusyLean.Independent.LadderBase
import BusyLean.SystemFLT.Trees

/-!
# The previous version of rung 4: the self-building transfinite ladder

This is rung 4 as it stood before the ladder with universe levels
(`Ladder.lean`). The current rung 4 incorporates it: every value of the current
rung includes the running maximum of `LadderOld.F4`, so the current rung is
larger (`contender_4_old_lt_contender_4`), and this version is dropped from
the hierarchy. It is kept, unchanged, only as that part of the current rung.

*Lengths.* The ladder of `LadderBase.lean`, with universes indexed by the
**addresses of a tree** `t` (`SystemFLT` over `Addr t`, a transfinite ladder of
the length of `t`), and with the Church tree type. A closed program of that
type, applied to inert constructors, denotes a well-founded tree
(`FLT.wt_of_treeTy`). One growth step joins `t` with the trees of all such
programs of depth `≤ n` (`grow`); growth iterates along a tree index
(`growAlong`).

*Reflection along trees.* `reflAlong τ` iterates ladder reflection along the
tree `τ`: the empty tree gives the successor function, `succ τ` gives
`ladderMax (reflAlong τ)` (the ladder with reflection along `τ` as its
oracle), and a limit takes the largest of its first `n + 1` branches.

*Self-building.* `selfTree n 0` grows the empty tree once, and
`selfTree n (k + 1)` grows `selfTree n k` along itself, using ladder programs
whose oracle is reflection along `selfTree n k`.

`F4 n` is reflection along `succ (selfTree n n)` at input `n`. Nothing here
mentions the lower rungs or any construction of the main tower.

**Do not evaluate `contender_4`.**
-/

namespace BusyLean.Indep.LadderOld

open BusyLean.FL
open BusyLean.Indep.Ladder (cross natsUpTo listMax kindsUpTo tysUpTo ladderMax)
open BusyLean.Ordinal (CTree Addr addr_wf addrUpTo)

variable {α : Type}

/-! ## Trees built by the transfinite ladder -/

/-- Church-style programs of the tree ladder (`SystemFLT`) of enumeration depth
`≤ n` over the atoms `as`. -/
def tctmsUpTo (as : List α) : Nat → List (FLT.CTm α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      let ts := tysUpTo as n
      let es := tctmsUpTo as n
      (natsUpTo n).map FLT.CTm.var ++
      ((cross ts es).map (fun p => FLT.CTm.lam p.1 p.2) ++
      ((cross es es).map (fun p => FLT.CTm.app p.1 p.2) ++
      ((cross ks es).map (fun p => FLT.CTm.tlam p.1 p.2) ++
      ((cross es ts).map (fun p => FLT.CTm.tapp p.1 p.2) ++
      (es.map FLT.CTm.klam0 ++
      ((cross es ks).map (fun p => FLT.CTm.kapp0 p.1 p.2) ++
      (es.map FLT.CTm.klam1 ++
      ((cross es ks).map (fun p => FLT.CTm.kapp1 p.1 p.2) ++
      [FLT.CTm.orc]))))))))

/-- The tree of a program over the addresses of `t` (type checked with `fuel`),
relative to the oracle `f`: defined when the program has the Church tree type,
and the empty tree otherwise. -/
def progTree (f : Nat → Nat) (t : CTree) (fuel : Nat) (p : FLT.CTm (Addr t)) : CTree :=
  match h : FLT.infer fuel [] [] p with
  | some A =>
      if hA : A = FLT.treeTy then
        FT.toTree f ⟨FLT.applyCons (FLT.erase p), FLT.wt_of_treeTy (FLT.wfUniv f (addr_wf t))
          (FLT.infer_sound fuel p (FLT.goodCtx_nil []) (h.trans (congrArg some hA))).1⟩
      else .zero
  | none => .zero

/-- One growth step: `t` joined with the trees of all programs of depth `≤ n`
over the addresses of `t` (type checked with fuel `n`, oracle `f`). -/
def grow (f : Nat → Nat) (n : Nat) (t : CTree) : CTree :=
  .lim fun i =>
    if i = 0 then t else ((tctmsUpTo (addrUpTo t n) n).map (progTree f t n)).getD (i - 1) .zero

/-- Growth steps iterated along a tree index, starting from `base`. -/
def growAlong (f : Nat → Nat) (n : Nat) (base : CTree) : CTree → CTree
  | .zero => base
  | .succ c => grow f n (growAlong f n base c)
  | .lim g => .lim fun i => growAlong f n base (g i)
  | .supL _ => base
  | .supH _ => base

/-! ## Reflection along trees -/

/-- Ladder reflection iterated along a tree: `succ τ` is the ladder with
reflection along `τ` as its oracle; a limit takes the largest of its first
`n + 1` branches. -/
def reflAlong : CTree → Nat → Nat
  | .zero => Nat.succ
  | .succ τ => ladderMax (reflAlong τ)
  | .lim g => fun n => listMax (fun i => reflAlong (g i) n) (natsUpTo (n + 1))
  | .supL _ => Nat.succ
  | .supH _ => Nat.succ

/-- The self-built trees: grow the empty tree once, then repeatedly grow the
tree along itself, with reflection along it as the oracle of the growing
programs. -/
def selfTree (n : Nat) : Nat → CTree
  | 0 => grow Nat.succ n .zero
  | k + 1 => growAlong (reflAlong (selfTree n k)) n (selfTree n k) (selfTree n k)

/-- Ladder reflection along `succ (selfTree n n)` at input `n`. -/
def F4 (n : Nat) : Nat := reflAlong (.succ (selfTree n n)) n

/-- **The previous rung 4**: the self-building transfinite ladder. Never evaluate it. -/
def contender_4 : Nat := F4 (F4 42)

end BusyLean.Indep.LadderOld
