import BusyLean.SystemFL.Ladder
import BusyLean.SystemFL.Church
import BusyLean.SystemF.Normalize

/-!
# Independent tower, rung 4: the ladder of universes and its values

The part of rung 4 shared by its versions (`Ladder.lean`, and the previous
version `LadderOld.lean`): the ladder of predicative universes over
dynamic-kind Fω (`BusyLean/SystemFL`, the language of Contender 14, used here as
a library), its programs enumerated by depth, and their values.

Its level-`ℓ` programs are Church-style terms with kind polymorphism at two
levels and `ℓ` universe atoms. One strong normalization proof covers every
level (`FL.sn_of_typed`), so a program's value (the Church numeral it
normalizes to) is computable. The language has an oracle constant
`orc : nat → nat`; `ladderMax g n` is `n + 1` plus the largest value of a
level-`n` program of depth `≤ n` with oracle `g`.
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

end BusyLean.Indep.Ladder
