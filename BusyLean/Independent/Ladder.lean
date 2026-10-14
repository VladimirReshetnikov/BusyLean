import BusyLean.SystemFL.Ladder
import BusyLean.SystemFL.Church
import BusyLean.SystemF.Normalize

/-!
# Independent tower, rung 3: the self-reflected ladder of universes

The third rung is an **impredicative** language: the ladder of predicative
universes over dynamic-kind Fω (`BusyLean/SystemFL`, the language of
Contender 14, used here as a library). Its level-`ℓ` programs are Church-style
terms with kind polymorphism at two levels and `ℓ` universe atoms. One strong
normalization proof covers every level (`FL.sn_of_typed`), so a program's value
(the Church numeral it normalizes to) is computable.

The language also has an oracle constant `orc : nat → nat`. Here the oracle is
**never another contender**. It is the previous stage of the same
construction:

* stage `0` is the successor function;
* stage `k + 1` maps `n` to `n + 1` plus the largest value of a level-`n` program
  of depth `≤ n` whose oracle is stage `k` (self-reflection).

`F3 n` is stage `n + 1` at input `n`, a diagonal over reflection stages,
universe levels and program sizes at once. Nothing below this line mentions
Contender 4, Contender 5, or any construction of the main tower.

**Do not evaluate `contender_3`.**
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

/-- Reflection stages: stage `k + 1` is the ladder maximum with stage `k` as
its oracle. -/
def stage : Nat → Nat → Nat
  | 0 => Nat.succ
  | k + 1 => ladderMax (stage k)

end BusyLean.Indep.Ladder

namespace BusyLean.Indep

/-- Reflection stage `n + 1` at input `n`. -/
def F3 (n : Nat) : Nat := Ladder.stage (n + 1) n

/-- **Rung 3**: the self-reflected ladder of universes. Never evaluate it. -/
def contender_3 : Nat := F3 (F3 42)

end BusyLean.Indep
