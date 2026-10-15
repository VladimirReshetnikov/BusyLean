import BusyLean.Independent.FwCheck
import BusyLean.Independent.TreeEmbedding

/-!
# The Takeuti–Feferman–Buchholz rung as one Fω program (proof infrastructure)

Types and combinators of the program, in the atom-free Fω syntax of
`FwCheck.lean`.

* `T0W = Tree nat` and `treeSW P = Tree P` are the trees of level `0` and of
  the level above `P`.
* `lvlW X = ∀C:★→★. (∀P. C P → C (Tree P)) → C T₀ → C X` is the **evidence**
  that `X` is a level type: a type-level Church numeral, with induction over
  the levels.
* `TWW` are the trees of level `ω`: a `sup` node carries its tag, the type of
  its branches and that type's evidence.
-/

namespace BusyLean.Indep.TFB

open BusyLean.Indep.FW

/-! ## Types -/

abbrev KA : FK := .arr .star .star

def natW : FTy := .all .star (.arr (.arr (.tvar 0) (.tvar 0)) (.arr (.tvar 0) (.tvar 0)))
def xxW : FTy := .arr (.tvar 0) (.tvar 0)
def lW : FTy := .arr (.arr natW (.tvar 0)) (.tvar 0)

/-- Brouwer trees. -/
def treeW : FTy := .all .star (.arr (.tvar 0) (.arr xxW (.arr lW (.tvar 0))))

/-- The handler of `sup` nodes branching over `E`. -/
def tPDW (E : FTy) : FTy := .arr natW (.arr (.arr E (.tvar 0)) (.tvar 0))

/-- Trees over the branching type `D` (`D` may mention outer type variables). -/
def treeSW (D : FTy) : FTy :=
  .all .star (.arr (.tvar 0) (.arr xxW (.arr lW (.arr (tPDW (D.ren Nat.succ)) (.tvar 0)))))

/-- Trees of level `0`. -/
def T0W : FTy := treeSW natW

/-- Evidence that `X` is a level type. -/
def lvlW (X : FTy) : FTy :=
  .all KA (.arr (.all .star (.arr (.app .star (.tvar 1) (.tvar 0)) (.app .star (.tvar 1) (treeSW (.tvar 0)))))
    (.arr (.app .star (.tvar 0) T0W) (.app .star (.tvar 0) (X.ren Nat.succ))))

/-- Trees of level `ω`. -/
def TWW : FTy :=
  .all .star (.arr (.tvar 0) (.arr xxW (.arr lW
    (.arr (.arr natW (.all .star (.arr (lvlW (.tvar 0)) (.arr (.arr (.tvar 0) (.tvar 1)) (.tvar 1)))))
      (.tvar 0)))))

/-! ## Church tuples -/

/-- `c₁ → ⋯ → cₙ → Z`. -/
def chainW : List FTy → FTy → FTy
  | [], Z => Z
  | c :: cs, Z => .arr c (chainW cs Z)

/-- `∀Z. (c₁ → ⋯ → cₙ → Z) → Z`. -/
def tupTy (cs : List FTy) : FTy := .all .star (.arr (chainW (cs.map (FTy.ren Nat.succ)) (.tvar 0)) (.tvar 0))

/-- `λ x₁ … xₙ. body`. -/
def lamsW : List FTy → FTm → FTm
  | [], b => b
  | c :: cs, b => .lam c (lamsW cs b)

/-- `f a₁ … aₙ`. -/
def appsW (f : FTm) : List FTm → FTm
  | [] => f
  | a :: as => appsW (.app f a) as

/-- `k x₁ … xₙ` for the variables `xᵢ = var (n - i)` under the binder of `k`. -/
def varsW (n : Nat) : List FTm := (List.range n).map fun i => .var (n - i)

/-- `λ x₁ … xₙ. ΛZ. λ k. k x₁ … xₙ`. -/
def mkTupW (cs : List FTy) : FTm :=
  lamsW cs (.tlam .star (.lam (chainW (cs.map (FTy.ren Nat.succ)) (.tvar 0))
    (appsW (.var 0) (varsW cs.length))))

/-- The tuple of `as`. -/
def tupleW (cs : List FTy) (as : List FTm) : FTm := appsW (mkTupW cs) as

/-- The `i`-th component of a tuple `o`. -/
def projW (cs : List FTy) (i : Nat) (o : FTm) : FTm :=
  .app (.tapp o (cs.getD i natW)) (lamsW cs (.var (cs.length - 1 - i)))

/-! ## Typed combinators (open types are shifted under type binders) -/

def tvW : FTy := .tvar 0

def app3W (u z s l : FTm) : FTm := .app (.app (.app u z) s) l
def app4W (u z s l p : FTm) : FTm := .app (app3W u z s l) p

def zeroW : FTm := .tlam .star (.lam xxW (.lam tvW (.var 0)))

def succW : FTm :=
  .lam natW (.tlam .star (.lam xxW (.lam tvW
    (.app (.var 1) (.app (.app (.tapp (.var 2) tvW) (.var 1)) (.var 0))))))

def pairTyW (A B : FTy) : FTy := .all .star (.arr (.arr (A.ren Nat.succ) (.arr (B.ren Nat.succ) tvW)) tvW)

def pairTmW (A B : FTy) : FTm :=
  .lam A (.lam B (.tlam .star (.lam (.arr (A.ren Nat.succ) (.arr (B.ren Nat.succ) tvW))
    (.app (.app (.var 0) (.var 2)) (.var 1)))))

def fstW (A B : FTy) (p : FTm) : FTm := .app (.tapp p A) (.lam A (.lam B (.var 1)))

def sndW (A B : FTy) (p : FTm) : FTm := .app (.tapp p B) (.lam A (.lam B (.var 0)))

def stepW (R : FTy) : FTm :=
  .lam (.arr natW (.arr R R)) (.lam (pairTyW natW R)
    (.app (.app (pairTmW natW R) (.app succW (fstW natW R (.var 0))))
      (.app (.app (.var 1) (fstW natW R (.var 0))) (sndW natW R (.var 0)))))

/-- Natural recursion at type `R`. -/
def recW (R : FTy) : FTm :=
  .lam R (.lam (.arr natW (.arr R R)) (.lam natW (sndW natW R
    (.app (.app (.tapp (.var 0) (pairTyW natW R)) (.app (stepW R) (.var 1)))
      (.app (.app (pairTmW natW R) zeroW) (.var 2))))))

def tzeroW : FTm := .tlam .star (.lam tvW (.lam xxW (.lam lW (.var 2))))

def tsuccW : FTm :=
  .lam treeW (.tlam .star (.lam tvW (.lam xxW (.lam lW
    (.app (.var 1) (app3W (.tapp (.var 3) tvW) (.var 2) (.var 1) (.var 0)))))))

def tlimW : FTm :=
  .lam (.arr natW treeW) (.tlam .star (.lam tvW (.lam xxW (.lam lW
    (.app (.var 0) (.lam natW (app3W (.tapp (.app (.var 4) (.var 0)) tvW) (.var 3) (.var 2) (.var 1))))))))

def foldW (R : FTy) : FTm :=
  .lam R (.lam (.arr R R) (.lam (.arr (.arr natW R) R) (.lam treeW
    (app3W (.tapp (.var 0) R) (.var 3) (.var 2) (.var 1)))))

def lzeroW (D : FTy) : FTm :=
  .tlam .star (.lam tvW (.lam xxW (.lam lW (.lam (tPDW (D.ren Nat.succ)) (.var 3)))))

def lsuccW (D : FTy) : FTm :=
  .lam (treeSW D) (.tlam .star (.lam tvW (.lam xxW (.lam lW (.lam (tPDW (D.ren Nat.succ))
    (.app (.var 2) (app4W (.tapp (.var 4) tvW) (.var 3) (.var 2) (.var 1) (.var 0))))))))

def llimW (D : FTy) : FTm :=
  .lam (.arr natW (treeSW D)) (.tlam .star (.lam tvW (.lam xxW (.lam lW (.lam (tPDW (D.ren Nat.succ))
    (.app (.var 1) (.lam natW
      (app4W (.tapp (.app (.var 5) (.var 0)) tvW) (.var 4) (.var 3) (.var 2) (.var 1)))))))))

def lsupW (D : FTy) : FTm :=
  .lam natW (.lam (.arr D (treeSW D)) (.tlam .star (.lam tvW (.lam xxW (.lam lW
    (.lam (tPDW (D.ren Nat.succ)) (.app (.app (.var 0) (.var 5)) (.lam (D.ren Nat.succ)
      (app4W (.tapp (.app (.var 5) (.var 0)) tvW) (.var 4) (.var 3) (.var 2) (.var 1))))))))))

def lfoldW (D R : FTy) : FTm :=
  .lam R (.lam (.arr R R) (.lam (.arr (.arr natW R) R)
    (.lam (.arr natW (.arr (.arr D R) R)) (.lam (treeSW D)
      (app4W (.tapp (.var 0) R) (.var 4) (.var 3) (.var 2) (.var 1))))))

/-! ## The typed translation of `TT`, relative to a base type `b` for level `0` -/

def levW (b : FTy) : Nat → FTy
  | 0 => b
  | m + 1 => treeSW (levW b m)

def tyTW (b : FTy) : TT.Ty → FTy
  | .nat => natW
  | .tree => treeW
  | .lev m => levW b m
  | .arr a c => .arr (tyTW b a) (tyTW b c)

def domW (b bd : FTy) : Nat → FTy
  | 0 => bd
  | m + 1 => levW b m

def trTW (b bd : FTy) : {Γ : List TT.Ty} → {σ : TT.Ty} → TT.Tm Γ σ → FTm
  | _, _, .var v => .var v.idx
  | _, _, @TT.Tm.lam _ a _ t => .lam (tyTW b a) (trTW b bd t)
  | _, _, .app s u => .app (trTW b bd s) (trTW b bd u)
  | _, _, .zero => zeroW
  | _, _, .succ => succW
  | _, _, .nrec r => recW (tyTW b r)
  | _, _, .tzero => tzeroW
  | _, _, .tsucc => tsuccW
  | _, _, .tlim => tlimW
  | _, _, .fold r => foldW (tyTW b r)
  | _, _, .lzero m => lzeroW (domW b bd m)
  | _, _, .lsucc m => lsuccW (domW b bd m)
  | _, _, .llim m => llimW (domW b bd m)
  | _, _, .lsup m => lsupW (levW b m)
  | _, _, .lsup0 => lsupW bd
  | _, _, .lfold0 r => lfoldW bd (tyTW b r)
  | _, _, .lfoldS m r => lfoldW (levW b m) (tyTW b r)

theorem eraseF_trTW (b bd : FTy) : ∀ {Γ : List TT.Ty} {σ : TT.Ty} (t : TT.Tm Γ σ),
    eraseF (trTW b bd t) = TT.utrT t
  | _, _, .var _ => rfl
  | _, _, .lam t => congrArg F.Tm.lam (eraseF_trTW b bd t)
  | _, _, .app s u => by
      show F.Tm.app (eraseF (trTW b bd s)) (eraseF (trTW b bd u)) = _
      rw [eraseF_trTW b bd s, eraseF_trTW b bd u]; rfl
  | _, _, .zero => rfl
  | _, _, .succ => rfl
  | _, _, .nrec _ => rfl
  | _, _, .tzero => rfl
  | _, _, .tsucc => rfl
  | _, _, .tlim => rfl
  | _, _, .fold _ => rfl
  | _, _, .lzero _ => rfl
  | _, _, .lsucc _ => rfl
  | _, _, .llim _ => rfl
  | _, _, .lsup _ => rfl
  | _, _, .lsup0 => rfl
  | _, _, .lfold0 _ => rfl
  | _, _, .lfoldS _ _ => rfl

end BusyLean.Indep.TFB
