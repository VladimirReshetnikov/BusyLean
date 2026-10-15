import BusyLean.SystemFL.Ladder
import BusyLean.SystemFL.Church
import BusyLean.SystemF.Normalize
import BusyLean.SystemFLT2.Numbers

/-!
# Independent tower, rung 4: the self-building ladder that reads what it builds

The fourth rung is an **impredicative** language that builds its own length
and reads it.

*Values.* The ladder of predicative universes over dynamic-kind Fω
(`BusyLean/SystemFL`, the language of Contender 14, used here as a library).
Its level-`ℓ` programs are Church-style terms with kind polymorphism at two
levels and `ℓ` universe atoms. One strong normalization proof covers every
level (`FL.sn_of_typed`), so a program's value (the Church numeral it
normalizes to) is computable. The language has an oracle constant
`orc : nat → nat`; `ladderMax g n` is `n + 1` plus the largest value of a
level-`n` program of depth `≤ n` with oracle `g`.

*Reading a tree.* The same ladder over System FT2's terms (`SystemFLT2`), with
universes indexed by the **addresses of a tree** `T`, gets a recursor over `T`
at every type. A program of the numeric reader type
`∀X. (∀Y. Y → (Y → Y) → ((nat → Y) → Y) → X → Y) → X → nat` is applied to the
recursor and to `T`, and normalizes (`FLT2.sn_of_natReaderTy`). A program of
the reader type also receives the tree constructors and builds a well-founded
tree from `T` (`FLT2.wt_of_readerTy`). Universes over unnamed atoms are out of
reach of a program of bounded depth (the truncation of the atom order), but the
tree itself is data: the same program computes more from a larger tree.

*Values that read the tree.* `readMax g T n` is `n + 1` plus the largest value of
a program of `ladderMax` and of a numeric reader program of depth `≤ n` over the
addresses of `T`, reading `T`, with oracle `g`.

*Growth by reading.* One jump joins `T` with the trees that all reader programs
of depth `≤ n` over the addresses of `T` build from `T` (`jump`); jumps iterate
along a tree index (`jumpAlong`).

*Reflection along trees.* `reflAlong T τ` iterates the reading reflection along
the tree `τ`: the empty tree gives the successor function, `succ τ` gives
`readMax (reflAlong T τ) T`, and a limit takes the largest of its first `n + 1`
branches.

*Self-building.* The trees are built by the ladder itself, and nothing else
seeds them: `selfTree n 0` is one jump from the empty tree, and
`selfTree n (k + 1)` jumps from `selfTree n k` along itself, with reflection
along it as the oracle of the reading programs.

`F4 n` is reflection along `succ (selfTree n n)`, reading `selfTree n n`, at
input `n`. Nothing below this line mentions the lower rungs (Contender 4,
Contender 5, the Hardy hierarchy, Buchholz's collapse), or any construction
of the main tower.

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

/-! ## Reading a tree with the ladder -/

open BusyLean.Ordinal (CTree Addr addr_wf addrUpTo)

/-- Church-style programs of the reading ladder (`SystemFLT2`) of enumeration
depth `≤ n` over the atoms `as`. -/
def rctmsUpTo (as : List α) : Nat → List (FLT2.CTm α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      let ts := tysUpTo as n
      let es := rctmsUpTo as n
      (natsUpTo n).map FLT2.CTm.var ++
      ((cross ts es).map (fun p => FLT2.CTm.lam p.1 p.2) ++
      ((cross es es).map (fun p => FLT2.CTm.app p.1 p.2) ++
      ((cross ks es).map (fun p => FLT2.CTm.tlam p.1 p.2) ++
      ((cross es ts).map (fun p => FLT2.CTm.tapp p.1 p.2) ++
      (es.map FLT2.CTm.klam0 ++
      ((cross es ks).map (fun p => FLT2.CTm.kapp0 p.1 p.2) ++
      (es.map FLT2.CTm.klam1 ++
      ((cross es ks).map (fun p => FLT2.CTm.kapp1 p.1 p.2) ++
      [FLT2.CTm.orc]))))))))

/-- The number a numeric reader program over the addresses of `T` computes from
`T` (type checked with `fuel`), with oracle `g`: `0` unless it has the numeric
reader type. -/
def readNat (g : Nat → Nat) (T : CTree) (fuel : Nat) (p : FLT2.CTm (Addr T)) : Nat :=
  match h : FLT2.infer fuel [] [] p with
  | some A =>
      if hA : A = FLT2.natReaderTy then
        FT2.decode (FT2.nf ⟨g, T⟩ ⟨FLT2.applyNatReader (FLT2.erase p),
          FLT2.sn_of_natReaderTy (FLT2.wfUniv ⟨g, T⟩ (addr_wf T))
            (FLT2.infer_sound fuel p (FLT2.goodCtx_nil []) (h.trans (congrArg some hA))).1⟩)
      else 0
  | none => 0

/-- The tree a reader program over the addresses of `T` builds from `T` (type
checked with `fuel`), with oracle `g`: `zero` unless it has the reader type. -/
def readTree (g : Nat → Nat) (T : CTree) (fuel : Nat) (p : FLT2.CTm (Addr T)) : CTree :=
  match h : FLT2.infer fuel [] [] p with
  | some A =>
      if hA : A = FLT2.readerTy then
        FT2.toTree ⟨g, T⟩ ⟨FLT2.applyReader (FLT2.erase p),
          FLT2.wt_of_readerTy (FLT2.wfUniv ⟨g, T⟩ (addr_wf T))
            (FLT2.infer_sound fuel p (FLT2.goodCtx_nil []) (h.trans (congrArg some hA))).1⟩
      else .zero
  | none => .zero

/-- `n + 1` plus the largest value of a program of `ladderMax g n` and of a
numeric reader program of depth `≤ n` over the addresses of `T`, reading `T`,
with oracle `g`. -/
def readMax (g : Nat → Nat) (T : CTree) (n : Nat) : Nat :=
  n + 1 + max (listMax (fvalue n g n) (ladderUpTo n))
    (listMax (readNat g T n) (rctmsUpTo (addrUpTo T n) n))

theorem ladderMax_le_readMax (g : Nat → Nat) (T : CTree) (n : Nat) :
    ladderMax g n ≤ readMax g T n :=
  Nat.add_le_add_left (Nat.le_max_left _ _) _

/-! ## Trees built by reading -/

/-- **The reading jump**: `t` joined with the trees that all reader programs of
depth `≤ n` over the addresses of `t` build from `t` (type checked with fuel
`n`, oracle `f`). -/
def jump (f : Nat → Nat) (n : Nat) (t : CTree) : CTree :=
  .lim fun i =>
    if i = 0 then t else ((rctmsUpTo (addrUpTo t n) n).map (readTree f t n)).getD (i - 1) .zero

/-- Jumps iterated along a tree index, starting from `base`. -/
def jumpAlong (f : Nat → Nat) (n : Nat) (base : CTree) : CTree → CTree
  | .zero => base
  | .succ c => jump f n (jumpAlong f n base c)
  | .lim g => .lim fun i => jumpAlong f n base (g i)
  | .supL _ => base
  | .supH _ => base

/-! ## Reflection along trees -/

/-- The reading reflection iterated along a tree: `succ τ` is `readMax` with
reflection along `τ` as its oracle, reading `T`; a limit takes the largest of
its first `n + 1` branches. -/
def reflAlong (T : CTree) : CTree → Nat → Nat
  | .zero => Nat.succ
  | .succ τ => readMax (reflAlong T τ) T
  | .lim g => fun n => listMax (fun i => reflAlong T (g i) n) (natsUpTo (n + 1))
  | .supL _ => Nat.succ
  | .supH _ => Nat.succ

/-- The self-built trees: one jump from the empty tree, then repeatedly jump from
the tree along itself, with reflection along it (reading it) as the oracle of
the reading programs. -/
def selfTree (n : Nat) : Nat → CTree
  | 0 => jump Nat.succ n .zero
  | k + 1 => jumpAlong (reflAlong (selfTree n k) (selfTree n k)) n (selfTree n k) (selfTree n k)

end BusyLean.Indep.Ladder

namespace BusyLean.Indep

/-- The reading reflection along `succ (selfTree n n)`, reading `selfTree n n`, at input `n`. -/
def F4 (n : Nat) : Nat := Ladder.reflAlong (Ladder.selfTree n n) (.succ (Ladder.selfTree n n)) n

/-- **Rung 4**: the self-building ladder that reads what it builds. Never evaluate it. -/
def contender_4 : Nat := F4 (F4 42)

end BusyLean.Indep
