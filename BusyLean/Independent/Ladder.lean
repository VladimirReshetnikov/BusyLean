import BusyLean.SystemFL.Ladder
import BusyLean.SystemFL.Church
import BusyLean.SystemF.Normalize
import BusyLean.SystemFLT.Trees

/-!
# Independent tower, rung 4: the self-building transfinite ladder

The fourth rung is an **impredicative** language that measures its own length.

*Values.* The ladder of predicative universes over dynamic-kind Fω
(`BusyLean/SystemFL`, the language of Contender 14, used here as a library).
Its level-`ℓ` programs are Church-style terms with kind polymorphism at two
levels and `ℓ` universe atoms. One strong normalization proof covers every
level (`FL.sn_of_typed`), so a program's value (the Church numeral it
normalizes to) is computable. The language has an oracle constant
`orc : nat → nat`; `ladderMax g n` is `n + 1` plus the largest value of a
level-`n` program of depth `≤ n` with oracle `g`.

*Lengths.* The same ladder, now with universes indexed by the **addresses of a
tree** `t` (`SystemFLT` over `Addr t`, a transfinite ladder of the length of
`t`), and with the Church tree type. A closed program of that type, applied to
inert constructors, denotes a well-founded tree (`FLT.wt_of_treeTy`). One
growth step joins `t` with the trees of all such programs of depth `≤ n`
(`grow`); growth iterates along a tree index (`growAlong`).

*Reflection along trees.* `reflAlong τ` iterates ladder reflection along the
tree `τ`: the empty tree gives the successor function, `succ τ` gives
`ladderMax (reflAlong τ)` (the ladder with reflection along `τ` as its
oracle), and a limit takes the largest of its first `n + 1` branches.

*Self-building.* The trees are built by the ladder itself, and nothing else
seeds them: `selfTree n 0` grows the empty tree once, and `selfTree n (k + 1)`
grows `selfTree n k` along itself, using ladder programs whose oracle is
reflection along `selfTree n k`.

`F4 n` is reflection along `succ (selfTree n n)` at input `n`. Nothing below
this line mentions the lower rungs (Contender 4, Contender 5, the Hardy
hierarchy at `ε₀`), or any construction of the main tower.

**Do not evaluate `contender_4`.**
-/

namespace BusyLean.Indep.Ladder

open BusyLean.FL

variable {α : Type}

/-! ## List utilities -/

def cross {A B : Type} (xs : List A) (ys : List B) : List (A × B) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

/-- `[n-1, …, 1, 0]`. -/
def natsUpTo : Nat → List Nat
  | 0 => []
  | n + 1 => n :: natsUpTo n

/-- The largest score in a list (`0` for the empty list). -/
def listMax {A : Type} (score : A → Nat) : List A → Nat
  | [] => 0
  | a :: xs => max (score a) (listMax score xs)

/-! ## Enumeration of kinds, types and programs by depth -/

/-- Kinds of enumeration depth `≤ n` over the atoms `as`. -/
def kindsUpTo (as : List α) : Nat → List (Kind α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      Kind.star :: (Kind.dyn :: ((cross ks ks).map (fun p => Kind.arr p.1 p.2) ++
        ((natsUpTo n).map Kind.kvar ++ ((natsUpTo n).map Kind.dvar ++ as.map Kind.atom))))

/-- Type constructors of enumeration depth `≤ n` over the atoms `as`. -/
def tysUpTo (as : List α) : Nat → List (Ty α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      let ts := tysUpTo as n
      (natsUpTo n).map Ty.tvar ++
      ((cross ts ts).map (fun p => Ty.arr p.1 p.2) ++
      ((cross ks ts).map (fun p => Ty.all p.1 p.2) ++
      ((cross ks ts).map (fun p => Ty.lam p.1 p.2) ++
      ((cross ks (cross ts ts)).map (fun p => Ty.app p.1 p.2.1 p.2.2) ++
      (ts.map Ty.kall0 ++ (ts.map Ty.kall1 ++
      ((cross ks ts).map (fun p => Ty.pack p.1 p.2) ++
      ((cross ks ts).map (fun p => Ty.unpack p.1 p.2) ++
      ((cross as (cross ks ts)).map (fun p => Ty.apack p.1 p.2.1 p.2.2) ++
      (cross as (cross ks ts)).map (fun p => Ty.aunpack p.1 p.2.1 p.2.2))))))))))

/-- Church-style programs of enumeration depth `≤ n` over the atoms `as`. -/
def ctmsUpTo (as : List α) : Nat → List (CTm α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      let ts := tysUpTo as n
      let es := ctmsUpTo as n
      (natsUpTo n).map CTm.var ++
      ((cross ts es).map (fun p => CTm.lam p.1 p.2) ++
      ((cross es es).map (fun p => CTm.app p.1 p.2) ++
      ((cross ks es).map (fun p => CTm.tlam p.1 p.2) ++
      ((cross es ts).map (fun p => CTm.tapp p.1 p.2) ++
      (es.map CTm.klam0 ++
      ((cross es ks).map (fun p => CTm.kapp0 p.1 p.2) ++
      (es.map CTm.klam1 ++
      ((cross es ks).map (fun p => CTm.kapp1 p.1 p.2) ++
      [CTm.orc]))))))))

/-! ## Values of programs -/

theorem sn_erase {f : Nat → Nat} (ℓ : Nat) {fuel : Nat} {t : CTm (Atom ℓ)}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (Univ f ℓ) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a level-`ℓ` program, type checked with `fuel`, relative to the
oracle `f`: the Church numeral it normalizes to (`0` if it is not a closed
program of type `nat`). -/
def fvalue (ℓ : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Atom ℓ)) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase ℓ (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Level-`n` programs of depth `≤ n`. -/
def ladderUpTo (n : Nat) : List (CTm (Atom n)) := ctmsUpTo (Atom.all n) n

/-- `n + 1` plus the largest value of a level-`n` program of depth `≤ n` (type
checked with fuel `n`) whose oracle is `g`. -/
def ladderMax (g : Nat → Nat) (n : Nat) : Nat :=
  n + 1 + listMax (fvalue n g n) (ladderUpTo n)

/-! ## Trees built by the transfinite ladder -/

open BusyLean.Ordinal (CTree Addr addr_wf addrUpTo)

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

end BusyLean.Indep.Ladder

namespace BusyLean.Indep

/-- Ladder reflection along `succ (selfTree n n)` at input `n`. -/
def F4 (n : Nat) : Nat := Ladder.reflAlong (.succ (Ladder.selfTree n n)) n

/-- **Rung 4**: the self-building transfinite ladder. Never evaluate it. -/
def contender_4 : Nat := F4 (F4 42)

end BusyLean.Indep
