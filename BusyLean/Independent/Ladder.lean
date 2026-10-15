import BusyLean.Independent.LadderBase
import BusyLean.Independent.LadderOld
import BusyLean.SystemFLV.Numbers

/-!
# Independent tower, rung 4: the self-building ladder with universe levels

The fourth rung is an **impredicative** language that builds its own length
and reads it.

*Values.* The ladder of predicative universes over dynamic-kind Fω
(`LadderBase.lean`): `ladderMax g n` is `n + 1` plus the largest value of a
level-`n` program of depth `≤ n` with oracle `g`.

*The ladder with universe levels.* The same ladder over System FT2's terms,
extended with **level variables** (`BusyLean/SystemFLV`): bounded
quantification `∀b ≤ l. A`, level-indexed operators `λb ≤ l. A` (of kind
`lfam l k`) with their applications, atoms at level variables, and level
abstraction and application in programs. Its universes are indexed by the
**addresses of a tree** `T`, so a program can quantify over all universes
below a given address. One normalization proof covers every universe over a
transitive well-founded atom order (`FLV.sn_of_typed`), the addresses of every
tree among them. A program has a recursor over `T` at every type: one of the
numeric reader type `∀X. (∀Y. Y → (Y → Y) → ((nat → Y) → Y) → X → Y) → X → nat`
is applied to the recursor and to `T`, and normalizes
(`FLV.sn_of_natReaderTy`); one of the reader type also receives the tree
constructors and builds a well-founded tree from `T` (`FLV.wt_of_readerTy`).

*Incorporating the previous rung 4.* Every value includes the running maximum
of the previous version of rung 4 (`LadderOld.F4`, the self-building
transfinite ladder of `SystemFLT`): `oldMax n` is the largest `LadderOld.F4 k`
for `k ≤ n`. So the current rung is larger than the previous one
(`contender_4_old_lt_contender_4` in `LadderOldLtLadder.lean`), and the previous
one is dropped from the hierarchy.

*Values that read the tree.* `readMax g T n` is `n + 1` plus the largest of
`oldMax n`, the values of the programs of `ladderMax g n`, and the values of
the numeric reader programs of depth `≤ n` over the addresses of `T`, reading
`T`, with oracle `g`.

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
open BusyLean.Ordinal (CTree Addr TreePath addr_wf addrUpTo)

variable {α : Type}

/-! ## Enumeration of the ladder with levels -/

/-- Levels of enumeration depth `n` over the atoms `as`: the level variables
below `n`, and the atoms. -/
def lvlsUpTo (as : List α) (n : Nat) : List (FLV.Lvl α) :=
  (natsUpTo n).map FLV.Lvl.var ++ as.map FLV.Lvl.const

/-- Kinds of the ladder with levels of enumeration depth `≤ n`. -/
def vkindsUpTo (as : List α) : Nat → List (FLV.Kind α)
  | 0 => []
  | n + 1 =>
      let ks := vkindsUpTo as n
      let ls := lvlsUpTo as n
      FLV.Kind.star :: (FLV.Kind.dyn :: ((cross ks ks).map (fun p => FLV.Kind.arr p.1 p.2) ++
        ((natsUpTo n).map FLV.Kind.kvar ++ ((natsUpTo n).map FLV.Kind.dvar ++
        (ls.map FLV.Kind.atom ++ (cross ls ks).map (fun p => FLV.Kind.lfam p.1 p.2))))))

/-- Type constructors of the ladder with levels of enumeration depth `≤ n`. -/
def vtysUpTo (as : List α) : Nat → List (FLV.Ty α)
  | 0 => []
  | n + 1 =>
      let ks := vkindsUpTo as n
      let ts := vtysUpTo as n
      let ls := lvlsUpTo as n
      (natsUpTo n).map FLV.Ty.tvar ++
      ((cross ts ts).map (fun p => FLV.Ty.arr p.1 p.2) ++
      ((cross ks ts).map (fun p => FLV.Ty.all p.1 p.2) ++
      ((cross ks ts).map (fun p => FLV.Ty.lam p.1 p.2) ++
      ((cross ks (cross ts ts)).map (fun p => FLV.Ty.app p.1 p.2.1 p.2.2) ++
      (ts.map FLV.Ty.kall0 ++ (ts.map FLV.Ty.kall1 ++
      ((cross ks ts).map (fun p => FLV.Ty.pack p.1 p.2) ++
      ((cross ks ts).map (fun p => FLV.Ty.unpack p.1 p.2) ++
      ((cross ls (cross ks ts)).map (fun p => FLV.Ty.apack p.1 p.2.1 p.2.2) ++
      ((cross ls (cross ks ts)).map (fun p => FLV.Ty.aunpack p.1 p.2.1 p.2.2) ++
      ((cross ls ts).map (fun p => FLV.Ty.lall p.1 p.2) ++
      ((cross ls ts).map (fun p => FLV.Ty.llam p.1 p.2) ++
      (cross ls (cross ts ls)).map (fun p => FLV.Ty.lapp p.1 p.2.1 p.2.2)))))))))))))

/-- Church-style programs of the ladder with levels of enumeration depth `≤ n`. -/
def vctmsUpTo (as : List α) : Nat → List (FLV.CTm α)
  | 0 => []
  | n + 1 =>
      let ks := vkindsUpTo as n
      let ts := vtysUpTo as n
      let ls := lvlsUpTo as n
      let es := vctmsUpTo as n
      (natsUpTo n).map FLV.CTm.var ++
      ((cross ts es).map (fun p => FLV.CTm.lam p.1 p.2) ++
      ((cross es es).map (fun p => FLV.CTm.app p.1 p.2) ++
      ((cross ks es).map (fun p => FLV.CTm.tlam p.1 p.2) ++
      ((cross es ts).map (fun p => FLV.CTm.tapp p.1 p.2) ++
      (es.map FLV.CTm.klam0 ++
      ((cross es ks).map (fun p => FLV.CTm.kapp0 p.1 p.2) ++
      (es.map FLV.CTm.klam1 ++
      ((cross es ks).map (fun p => FLV.CTm.kapp1 p.1 p.2) ++
      ((cross ls es).map (fun p => FLV.CTm.llam p.1 p.2) ++
      ((cross es ls).map (fun p => FLV.CTm.lapp p.1 p.2) ++
      [FLV.CTm.orc]))))))))))

/-! ## Reading a tree with the ladder with levels -/

/-- The descendant order on the addresses of a tree is transitive. -/
theorem addr_ltTrans (T : CTree) : FLV.LtTrans (Addr T) :=
  fun _ _ _ h1 h2 => TreePath.lt_trans T h1 h2

/-- The number a numeric reader program over the addresses of `T` computes from
`T` (type checked with `fuel`), with oracle `g`: `0` unless it has the numeric
reader type. -/
def readNat (g : Nat → Nat) (T : CTree) (fuel : Nat) (p : FLV.CTm (Addr T)) : Nat :=
  match h : FLV.infer fuel [] [] [] p with
  | some A =>
      if hA : A = FLV.natReaderTy then
        FT2.decode (FT2.nf ⟨g, T⟩ ⟨FLT2.applyNatReader (FLV.erase p),
          FLV.sn_of_natReaderTy (FLT2.wfUniv ⟨g, T⟩ (addr_wf T)) (addr_ltTrans T)
            (TreePath.root : Addr T)
            (FLV.infer_sound (addr_ltTrans T) fuel p (FLV.goodCtx_nil [] [])
              (h.trans (congrArg some hA))).1⟩)
      else 0
  | none => 0

/-- The tree a reader program over the addresses of `T` builds from `T` (type
checked with `fuel`), with oracle `g`: `zero` unless it has the reader type. -/
def readTree (g : Nat → Nat) (T : CTree) (fuel : Nat) (p : FLV.CTm (Addr T)) : CTree :=
  match h : FLV.infer fuel [] [] [] p with
  | some A =>
      if hA : A = FLV.readerTy then
        FT2.toTree ⟨g, T⟩ ⟨FLT2.applyReader (FLV.erase p),
          FLV.wt_of_readerTy (FLT2.wfUniv ⟨g, T⟩ (addr_wf T)) (addr_ltTrans T)
            (TreePath.root : Addr T)
            (FLV.infer_sound (addr_ltTrans T) fuel p (FLV.goodCtx_nil [] [])
              (h.trans (congrArg some hA))).1⟩
      else .zero
  | none => .zero

/-- The running maximum of the previous rung 4: the largest `LadderOld.F4 k`
for `k ≤ n`. -/
def oldMax (n : Nat) : Nat := listMax LadderOld.F4 (natsUpTo (n + 1))

/-- `n + 1` plus the largest of `oldMax n`, the values of the programs of
`ladderMax g n`, and the values of the numeric reader programs of depth `≤ n`
over the addresses of `T`, reading `T`, with oracle `g`. -/
def readMax (g : Nat → Nat) (T : CTree) (n : Nat) : Nat :=
  n + 1 + max (oldMax n) (max (listMax (fvalue n g n) (ladderUpTo n))
    (listMax (readNat g T n) (vctmsUpTo (addrUpTo T n) n)))

theorem ladderMax_le_readMax (g : Nat → Nat) (T : CTree) (n : Nat) :
    ladderMax g n ≤ readMax g T n :=
  Nat.add_le_add_left (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) _

theorem oldMax_lt_readMax (g : Nat → Nat) (T : CTree) (n : Nat) : oldMax n < readMax g T n := by
  unfold readMax
  have h := Nat.le_max_left (oldMax n) (max (listMax (fvalue n g n) (ladderUpTo n))
    (listMax (readNat g T n) (vctmsUpTo (addrUpTo T n) n)))
  generalize max (oldMax n) (max (listMax (fvalue n g n) (ladderUpTo n))
    (listMax (readNat g T n) (vctmsUpTo (addrUpTo T n) n))) = M at h ⊢
  generalize oldMax n = O at h ⊢
  omega

/-! ## Trees built by reading -/

/-- **The reading jump**: `t` joined with the trees that all reader programs of
depth `≤ n` over the addresses of `t` build from `t` (type checked with fuel
`n`, oracle `f`). -/
def jump (f : Nat → Nat) (n : Nat) (t : CTree) : CTree :=
  .lim fun i =>
    if i = 0 then t else ((vctmsUpTo (addrUpTo t n) n).map (readTree f t n)).getD (i - 1) .zero

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

/-- **Rung 4**: the self-building ladder with universe levels, which reads what it
builds. Never evaluate it. -/
def contender_4 : Nat := F4 (F4 42)

end BusyLean.Indep
