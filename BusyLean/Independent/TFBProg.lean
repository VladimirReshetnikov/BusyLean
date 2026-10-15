import BusyLean.Independent.FwCheck
import BusyLean.Independent.TreeEmbedding

/-!
# The Takeuti–Feferman–Buchholz rung as one Fω program (proof infrastructure)

The program computes `ψ_0(ε_{Ω_ω+1})` (`Buch.thetaTFB`) as a Brouwer tree. It is
written in the atom-free Fω syntax of `FwCheck.lean`.

* `treeSW E = Tree E` are the trees branching over `E`. The trees of level `m`
  are `Tree (P m)` for the **branching types** `P 0 = nat` and
  `P (m + 1) = Tree (P m)`.
* `lvlW E = ∀C:★→★. (∀P. C P → C (Tree P)) → C nat → C E` is the **evidence**
  that `E` is a branching type: a type-level Church numeral, which gives
  induction over the levels (`indLW`, a paramorphism).
* `TWW` are the trees of level `ω`. A `sup` node carries its tag, the branching
  type `D` of its branches `Tree D` and the evidence for `D`.

Every combinator is closed and **λ-lifted**: inside its body, the only
λ-abstractions are within other closed combinators. So each combinator's erasure
is `λx₁ … xₙ. b` where `b` only applies closed terms and variables, and one
β-reduction lemma describes it.
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

/-- `C A` for a type operator `C : ★ → ★`. -/
def apW (C A : FTy) : FTy := .app .star C A

/-- `∀P. C P → C (Tree P)`, for the motive `C = tvar 0`. -/
def lvlStepTy : FTy := .all .star (.arr (apW (.tvar 1) (.tvar 0)) (apW (.tvar 1) (treeSW (.tvar 0))))

/-- Evidence that `E` is a branching type. -/
def lvlW (E : FTy) : FTy :=
  .all KA (.arr lvlStepTy (.arr (apW (.tvar 0) natW) (apW (.tvar 0) (E.ren Nat.succ))))

/-- The handler of `sup` nodes of level `ω`, with result `X = tvar 0`. -/
def supHW : FTy :=
  .arr natW (.all .star (.arr (lvlW (.tvar 0)) (.arr (.arr (treeSW (.tvar 0)) (.tvar 1)) (.tvar 1))))

/-- Trees of level `ω`. -/
def TWW : FTy := .all .star (.arr (.tvar 0) (.arr xxW (.arr lW (.arr supHW (.tvar 0)))))

/-- The result type of the collapse: `∀E. Lvl E → nat → Tree E`. -/
def rTy : FTy := .all .star (.arr (lvlW (.tvar 0)) (.arr natW (treeSW (.tvar 0))))

/-! ## Basic combinators -/

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

/-! ## The typed translation of `TT`, with an arbitrary type for each level

`trTL lv dom t` translates a `TT` term whose levels `m` stand for the types
`lv m` with branching types `dom m`. -/

def tyTL (lv : Nat → FTy) : TT.Ty → FTy
  | .nat => natW
  | .tree => treeW
  | .lev m => lv m
  | .arr a c => .arr (tyTL lv a) (tyTL lv c)

def trTL (lv dom : Nat → FTy) : {Γ : List TT.Ty} → {σ : TT.Ty} → TT.Tm Γ σ → FTm
  | _, _, .var v => .var v.idx
  | _, _, @TT.Tm.lam _ a _ t => .lam (tyTL lv a) (trTL lv dom t)
  | _, _, .app s u => .app (trTL lv dom s) (trTL lv dom u)
  | _, _, .zero => zeroW
  | _, _, .succ => succW
  | _, _, .nrec r => recW (tyTL lv r)
  | _, _, .tzero => tzeroW
  | _, _, .tsucc => tsuccW
  | _, _, .tlim => tlimW
  | _, _, .fold r => foldW (tyTL lv r)
  | _, _, .lzero m => lzeroW (dom m)
  | _, _, .lsucc m => lsuccW (dom m)
  | _, _, .llim m => llimW (dom m)
  | _, _, .lsup m => lsupW (lv m)
  | _, _, .lsup0 => lsupW (dom 0)
  | _, _, .lfold0 r => lfoldW (dom 0) (tyTL lv r)
  | _, _, .lfoldS m r => lfoldW (lv m) (tyTL lv r)

theorem eraseF_trTL (lv dom : Nat → FTy) : ∀ {Γ : List TT.Ty} {σ : TT.Ty} (t : TT.Tm Γ σ),
    eraseF (trTL lv dom t) = TT.utrT t
  | _, _, .var _ => rfl
  | _, _, .lam t => congrArg F.Tm.lam (eraseF_trTL lv dom t)
  | _, _, .app s u => by
      show F.Tm.app (eraseF (trTL lv dom s)) (eraseF (trTL lv dom u)) = _
      rw [eraseF_trTL lv dom s, eraseF_trTL lv dom u]; rfl
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

/-- A map of four levels: `lv 0 = a₀`, …, `lv 3 = a₃` (the rest unused). -/
def lv4 (a0 a1 a2 a3 : FTy) : Nat → FTy
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | _ => a3

/-! ## Evidence and induction over the levels -/

/-- The evidence for `nat`. -/
def ev0W : FTm := .tlam KA (.lam lvlStepTy (.lam (apW (.tvar 0) natW) (.var 0)))

/-- `∀E. Lvl E → Lvl (Tree E)`. -/
def evStepW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.tlam KA (.lam lvlStepTy (.lam (apW (.tvar 0) natW)
    (.app (.tapp (.var 1) (.tvar 1)) (.app (.app (.tapp (.var 2) (.tvar 0)) (.var 1)) (.var 0)))))))

/-- The step of a paramorphism, for the motive `C = tvar 0`: `∀P. Lvl P → C P → C (Tree P)`. -/
def pstepTy : FTy :=
  .all .star (.arr (lvlW (.tvar 0)) (.arr (apW (.tvar 1) (.tvar 0)) (apW (.tvar 1) (treeSW (.tvar 0)))))

/-- `pair (Lvl Y) (C Y)` with `Y = tvar 0`, `C = tvar 1`. -/
def evPairTy : FTy := pairTyW (lvlW (.tvar 0)) (apW (.tvar 1) (.tvar 0))

/-- `ΛC. λs. ΛY. λp. ⟨evStep (fst p), s (fst p) (snd p)⟩`. -/
def stepLW : FTm :=
  .tlam KA (.lam pstepTy (.tlam .star (.lam evPairTy
    (.app (.app (pairTmW (lvlW (treeSW (.tvar 0))) (apW (.tvar 1) (treeSW (.tvar 0))))
        (.app (.tapp evStepW (.tvar 0)) (fstW (lvlW (.tvar 0)) (apW (.tvar 1) (.tvar 0)) (.var 0))))
      (.app (.app (.tapp (.var 1) (.tvar 0)) (fstW (lvlW (.tvar 0)) (apW (.tvar 1) (.tvar 0)) (.var 0)))
        (sndW (lvlW (.tvar 0)) (apW (.tvar 1) (.tvar 0)) (.var 0)))))))

/-- **Induction over the levels**:
`∀E. Lvl E → ∀C:★→★. (∀P. Lvl P → C P → C (Tree P)) → C nat → C E`. -/
def indLW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.tlam KA (.lam pstepTy (.lam (apW (.tvar 0) natW)
    (sndW (lvlW (.tvar 1)) (apW (.tvar 0) (.tvar 1))
      (.app (.app (.tapp (.var 2) (.lam .star evPairTy)) (.app (.tapp stepLW (.tvar 0)) (.var 1)))
        (.app (.app (pairTmW (lvlW natW) (apW (.tvar 0) natW)) ev0W) (.var 0))))))))

/-- `indL [E] ev [C] s b`. -/
def indL (E : FTy) (ev : FTm) (C : FTy) (s b : FTm) : FTm :=
  .app (.app (.tapp (.app (.tapp indLW E) ev) C) s) b

/-- The level `m` of the branching type `P m`. -/
def lvlOfW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.app (.app (.tapp (.var 0) (.lam .star natW)) (.tlam .star succW)) zeroW))

/-! ## Conversions between levels -/

/-- `∀D. Tree nat → Tree D`: from level `0`, dropping every `sup`. -/
def raiseW : FTm :=
  .tlam .star (trTL (lv4 T0W (.tvar 0) (treeSW (.tvar 0)) (treeSW (.tvar 0)))
    (lv4 natW natW (.tvar 0) (.tvar 0)) (TT.raiseT 2 (Γ := [])))

/-- `∀D. Tree D → Tree nat`: to level `0`, dropping every `sup`. -/
def dropW : FTm :=
  .tlam .star (trTL (lv4 T0W (.tvar 0) (treeSW (.tvar 0)) (treeSW (.tvar 0)))
    (lv4 natW natW (.tvar 0) (.tvar 0)) (TT.dropT 1 (Γ := [])))

/-- `∀E D. nat → (Tree D → Tree E) → Tree (Tree E) → Tree (Tree D)`: `λ thr h. cmap thr h`. -/
def cmapW : FTm :=
  .tlam .star (.tlam .star (trTL
    (lv4 (treeSW (.tvar 1)) (treeSW (treeSW (.tvar 1))) (treeSW (.tvar 0)) (treeSW (treeSW (.tvar 0))))
    (lv4 (.tvar 1) (treeSW (.tvar 1)) (.tvar 0) (treeSW (.tvar 0))) (TT.cmapT 0 2 (Γ := []))))

/-- `∀D. Lvl D → (Tree E → Tree D) × (Tree D → Tree E)`. -/
def ccTy (E : FTy) : FTy :=
  .all .star (.arr (lvlW (.tvar 0)) (pairTyW (.arr (treeSW (E.ren Nat.succ)) (treeSW (.tvar 0)))
    (.arr (treeSW (.tvar 0)) (treeSW (E.ren Nat.succ)))))

/-- `(Tree (Tree E) → Tree D) × (Tree D → Tree (Tree E))`. -/
def mdTy (E D : FTy) : FTy :=
  pairTyW (.arr (treeSW (treeSW E)) (treeSW D)) (.arr (treeSW D) (treeSW (treeSW E)))

/-- Conversions from level `0`. -/
def convBaseW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0))
    (.app (.app (pairTmW (.arr T0W (treeSW (.tvar 0))) (.arr (treeSW (.tvar 0)) T0W))
      (.tapp raiseW (.tvar 0))) (.tapp dropW (.tvar 0))))

/-- Conversions from level `m + 1` to level `0`. -/
def cBaseDW : FTm :=
  .tlam .star
    (.app (.app (pairTmW (.arr (treeSW (treeSW (.tvar 0))) T0W) (.arr T0W (treeSW (treeSW (.tvar 0)))))
      (.tapp dropW (treeSW (.tvar 0)))) (.tapp raiseW (treeSW (.tvar 0))))

/-- Conversions from level `m + 1` to level `j + 1`, from those between `m` and `j`. -/
def cStepDW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.lam (ccTy (.tvar 0)) (.tlam .star (.lam (lvlW (.tvar 0))
    (.lam (mdTy (.tvar 1) (.tvar 0))
      (.app (.app (pairTmW (.arr (treeSW (treeSW (.tvar 1))) (treeSW (treeSW (.tvar 0))))
          (.arr (treeSW (treeSW (.tvar 0))) (treeSW (treeSW (.tvar 1)))))
        (.app (.app (.tapp (.tapp cmapW (.tvar 1)) (.tvar 0))
            (.app succW (.app (.tapp lvlOfW (.tvar 0)) (.var 1))))
          (sndW (.arr (treeSW (.tvar 1)) (treeSW (.tvar 0))) (.arr (treeSW (.tvar 0)) (treeSW (.tvar 1)))
            (.app (.tapp (.var 2) (.tvar 0)) (.var 1)))))
        (.app (.app (.tapp (.tapp cmapW (.tvar 0)) (.tvar 1))
            (.app succW (.app (.tapp lvlOfW (.tvar 1)) (.var 3))))
          (fstW (.arr (treeSW (.tvar 1)) (treeSW (.tvar 0))) (.arr (treeSW (.tvar 0)) (treeSW (.tvar 1)))
            (.app (.tapp (.var 2) (.tvar 0)) (.var 1))))))))))

/-- Conversions from level `m + 1`, by induction on the other level. -/
def convStepW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.lam (ccTy (.tvar 0)) (.tlam .star (.lam (lvlW (.tvar 0))
    (indL (.tvar 0) (.var 0) (.lam .star (mdTy (.tvar 2) (.tvar 0)))
      (.app (.app (.tapp cStepDW (.tvar 1)) (.var 2)) (.var 1))
      (.tapp cBaseDW (.tvar 1)))))))

/-- **Conversions between any two levels**:
`∀E. Lvl E → ∀D. Lvl D → (Tree E → Tree D) × (Tree D → Tree E)`. -/
def convW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0))
    (indL (.tvar 0) (.var 0) (.lam .star (ccTy (.tvar 0))) convStepW convBaseW))

/-! ## `sup`s with branches given on another level -/

/-- `nat → ∀D. Lvl D → (Tree D → Tree E) → Tree E`. -/
def svTy (E : FTy) : FTy :=
  .arr natW (.all .star (.arr (lvlW (.tvar 0))
    (.arr (.arr (treeSW (.tvar 0)) (treeSW (E.ren Nat.succ))) (treeSW (E.ren Nat.succ)))))

/-- `λ μ. sup μ (λ _. 0)` at level `0`. -/
def supV0W : FTm := trTL (lv4 T0W T0W T0W T0W) (lv4 natW natW natW natW) (TT.supVia0T (Γ := []))

def svBaseW : FTm :=
  .lam natW (.tlam .star (.lam (lvlW (.tvar 0)) (.lam (.arr (treeSW (.tvar 0)) T0W)
    (.app supV0W (.var 2)))))

/-- `ΛA B C. λ g f x. g (f x)`. -/
def composeW : FTm :=
  .tlam .star (.tlam .star (.tlam .star
    (.lam (.arr (.tvar 1) (.tvar 0)) (.lam (.arr (.tvar 2) (.tvar 1)) (.lam (.tvar 2)
      (.app (.var 2) (.app (.var 1) (.var 0))))))))

def svStepW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.lam (svTy (.tvar 0)) (.lam natW (.tlam .star
    (.lam (lvlW (.tvar 0)) (.lam (.arr (treeSW (.tvar 0)) (treeSW (treeSW (.tvar 1))))
      (.app (.app (lsupW (treeSW (.tvar 1))) (.var 2))
        (.app (.app (.tapp (.tapp (.tapp composeW (treeSW (.tvar 1))) (treeSW (.tvar 0)))
              (treeSW (treeSW (.tvar 1)))) (.var 0))
          (fstW (.arr (treeSW (.tvar 1)) (treeSW (.tvar 0))) (.arr (treeSW (.tvar 0)) (treeSW (.tvar 1)))
            (.app (.tapp (.app (.tapp convW (.tvar 1)) (.var 4)) (.tvar 0)) (.var 1)))))))))))

/-- **`supVia`**: `∀E. Lvl E → nat → ∀D. Lvl D → (Tree D → Tree E) → Tree E`. -/
def supViaW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0))
    (indL (.tvar 0) (.var 0) (.lam .star (svTy (.tvar 0))) svStepW svBaseW))

/-! ## Trees of level `ω` -/

def zeroTWW : FTm := .tlam .star (.lam tvW (.lam xxW (.lam lW (.lam supHW (.var 3)))))

def succTWW : FTm :=
  .lam TWW (.tlam .star (.lam tvW (.lam xxW (.lam lW (.lam supHW
    (.app (.var 2) (app4W (.tapp (.var 4) tvW) (.var 3) (.var 2) (.var 1) (.var 0))))))))

def limTWW : FTm :=
  .lam (.arr natW TWW) (.tlam .star (.lam tvW (.lam xxW (.lam lW (.lam supHW
    (.app (.var 1) (.lam natW
      (app4W (.tapp (.app (.var 5) (.var 0)) tvW) (.var 4) (.var 3) (.var 2) (.var 1)))))))))

/-- `nat → ∀D. Lvl D → (Tree D → TW) → TW`. -/
def supTWW : FTm :=
  .lam natW (.tlam .star (.lam (lvlW (.tvar 0)) (.lam (.arr (treeSW (.tvar 0)) TWW)
    (.tlam .star (.lam tvW (.lam xxW (.lam lW (.lam supHW
      (.app (.app (.tapp (.app (.var 0) (.var 6)) (.tvar 1)) (.var 5))
        (.lam (treeSW (.tvar 1))
          (app4W (.tapp (.app (.var 5) (.var 0)) tvW) (.var 4) (.var 3) (.var 2) (.var 1))))))))))))

/-- Trees of level `0` as trees of level `ω` (`sup`s become `0`). -/
def embSup0W : FTm := .lam natW (.lam (.arr natW TWW) zeroTWW)

def embBaseW : FTm := .lam T0W (app4W (.tapp (.var 0) TWW) zeroTWW succTWW limTWW embSup0W)

/-- `ΛE. λ ev μ g. sup μ [E] ev g`. -/
def embHW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.lam natW (.lam (.arr (treeSW (.tvar 0)) TWW)
    (.app (.app (.tapp (.app supTWW (.var 1)) (.tvar 0)) (.var 2)) (.var 0)))))

def embStepW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.lam (.arr (treeSW (.tvar 0)) TWW)
    (.lam (treeSW (treeSW (.tvar 0)))
      (app4W (.tapp (.var 0) TWW) zeroTWW succTWW limTWW (.app (.tapp embHW (.tvar 0)) (.var 2))))))

/-- **Trees of level `m` as trees of level `ω`**: `∀E. Lvl E → Tree E → TW`. -/
def embW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0))
    (indL (.tvar 0) (.var 0) (.lam .star (.arr (treeSW (.tvar 0)) TWW)) embStepW embBaseW))

def addTWW : FTm := .lam TWW (.lam TWW (app4W (.tapp (.var 0) TWW) (.var 1) succTWW limTWW supTWW))

/-- `λ a r. r + a`. -/
def flipAddW : FTm := .lam TWW (.lam TWW (.app (.app addTWW (.var 0)) (.var 1)))

def mulTWW : FTm :=
  .lam TWW (.lam TWW (app4W (.tapp (.var 0) TWW) zeroTWW (.app flipAddW (.var 1)) limTWW supTWW))

/-- Packages `∃E. Lvl E`, impredicatively: `∀R. (∀E. Lvl E → R) → R`. -/
def pkgTy : FTy := .all .star (.arr (.all .star (.arr (lvlW (.tvar 0)) (.tvar 1))) (.tvar 0))

def pkg0W : FTm :=
  .tlam .star (.lam (.all .star (.arr (lvlW (.tvar 0)) (.tvar 1))) (.app (.tapp (.var 0) natW) ev0W))

def kStepW : FTm :=
  .tlam .star (.lam (.all .star (.arr (lvlW (.tvar 0)) (.tvar 1)))
    (.tlam .star (.lam (lvlW (.tvar 0))
      (.app (.tapp (.var 1) (treeSW (.tvar 0))) (.app (.tapp evStepW (.tvar 0)) (.var 0))))))

def pkgStepW : FTm :=
  .lam pkgTy (.tlam .star (.lam (.all .star (.arr (lvlW (.tvar 0)) (.tvar 1)))
    (.app (.tapp (.var 1) (.tvar 0)) (.app (.tapp kStepW (.tvar 0)) (.var 0)))))

/-- The branching type `P n` with its evidence. -/
def lvlPkgW : FTm := .lam natW (.app (.app (.tapp (.var 0) pkgTy) pkgStepW) pkg0W)

/-- `λ n. ΛE. λ ev. sup n [E] ev (emb [E] ev)`. -/
def omKW : FTm :=
  .lam natW (.tlam .star (.lam (lvlW (.tvar 0))
    (.app (.app (.tapp (.app supTWW (.var 1)) (.tvar 0)) (.var 0)) (.app (.tapp embW (.tvar 0)) (.var 0)))))

/-- `Ω_{n+1}`, the limit of all trees of level `n`. -/
def omegaTWW : FTm := .lam natW (.app (.tapp (.app lvlPkgW (.var 0)) TWW) (.app omKW (.var 0)))

/-- `Ω_ω`. -/
def omegaOmegaW : FTm := .app limTWW omegaTWW

def mulOOW : FTm := .lam TWW (.app (.app mulTWW (.var 0)) omegaOmegaW)

/-- `Ω_ω^a`. -/
def opowTWW : FTm :=
  .lam TWW (app4W (.tapp (.var 0) TWW) (.app succTWW zeroTWW) mulOOW limTWW supTWW)

def towerTWW : FTm := .lam natW (.app (.app (.tapp (.var 0) TWW) opowTWW) (.app omegaTWW zeroW))

/-- `ε_{Ω_ω+1}`. -/
def epsTWW : FTm := .app limTWW towerTWW

/-! ## The collapse -/

/-- `ΛA. λx. x`. -/
def idW : FTm := .tlam .star (.lam (.tvar 0) (.var 0))

def omStepW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.lam natW (.lam (treeSW (.tvar 0))
    (.app (.app (.tapp (.app (.app (.tapp supViaW (.tvar 0)) (.var 2)) (.var 1)) (.tvar 0)) (.var 2))
      (.tapp idW (treeSW (.tvar 0)))))))

/-- **`Ω_ν` at any level**: `∀E. Lvl E → nat → Tree E`. -/
def omegaOfW : FTm :=
  .tlam .star (.lam (lvlW (.tvar 0)) (.lam natW
    (.app (.app (.app (recW (treeSW (.tvar 0))) (.app (lsuccW (.tvar 0)) (lzeroW (.tvar 0))))
      (.app (.tapp omStepW (.tvar 0)) (.var 1))) (.var 0))))

/-- `∀E. Tree E → nat → Tree E`: `a · k`. -/
def mulNatW : FTm :=
  .tlam .star (trTL (lv4 (.tvar 0) (treeSW (.tvar 0)) (.tvar 0) (.tvar 0))
    (lv4 (.tvar 0) (.tvar 0) (.tvar 0) (.tvar 0)) (TT.mulNatL 0 (Γ := [])))

/-- `∀E. nat → nat → Tree E → Tree E → Tree E`: `λ μ c a b. if μ < c then a else b`. -/
def ifLtW : FTm :=
  .tlam .star (trTL (lv4 (treeSW (.tvar 0)) (treeSW (.tvar 0)) (treeSW (.tvar 0)) (treeSW (.tvar 0)))
    (lv4 (.tvar 0) (.tvar 0) (.tvar 0) (.tvar 0)) (TT.ifLtC (r := .lev 0) (Γ := [])))

def sPsiW : FTm :=
  .lam rTy (.tlam .star (.lam (lvlW (.tvar 0)) (.lam natW
    (.app (llimW (.tvar 0)) (.app (.tapp mulNatW (.tvar 0))
      (.app (.app (.tapp (.var 2) (.tvar 0)) (.var 1)) (.var 0)))))))

/-- `ΛE. λ g ev ν k. g k [E] ev ν`. -/
def lkW : FTm :=
  .tlam .star (.lam (.arr natW rTy) (.lam (lvlW (.tvar 0)) (.lam natW (.lam natW
    (.app (.app (.tapp (.app (.var 3) (.var 0)) (.tvar 0)) (.var 2)) (.var 1))))))

def lPsiW : FTm :=
  .lam (.arr natW rTy) (.tlam .star (.lam (lvlW (.tvar 0)) (.lam natW
    (.app (llimW (.tvar 0)) (.app (.app (.app (.tapp lkW (.tvar 0)) (.var 2)) (.var 1)) (.var 0))))))

/-- `ΛD E. λ rs ev ν d. rs d [E] ev ν`. -/
def kkW : FTm :=
  .tlam .star (.tlam .star (.lam (.arr (treeSW (.tvar 1)) rTy) (.lam (lvlW (.tvar 0)) (.lam natW
    (.lam (treeSW (.tvar 1))
      (.app (.app (.tapp (.app (.var 3) (.var 0)) (.tvar 0)) (.var 2)) (.var 1)))))))

/-- `ΛD. λ μ evD rs _ g. rs g [D] evD μ`. -/
def dStepW : FTm :=
  .tlam .star (.lam natW (.lam (lvlW (.tvar 0)) (.lam (.arr (treeSW (.tvar 0)) rTy) (.lam natW
    (.lam (treeSW (.tvar 0))
      (.app (.app (.tapp (.app (.var 2) (.var 0)) (.tvar 0)) (.var 3)) (.var 4)))))))

/-- `ΛD E. λ μ evD rs evE ν k. rs (g_k) [E] evE ν` with `g_0 = Ω_μ`, `g_{k+1} = ψ_μ(rs g_k)`. -/
def dkW : FTm :=
  .tlam .star (.tlam .star (.lam natW (.lam (lvlW (.tvar 1)) (.lam (.arr (treeSW (.tvar 1)) rTy)
    (.lam (lvlW (.tvar 0)) (.lam natW (.lam natW
      (.app (.app (.tapp (.app (.var 3)
          (.app (.app (.app (recW (treeSW (.tvar 1)))
              (.app (.app (.tapp omegaOfW (.tvar 1)) (.var 4)) (.var 5)))
            (.app (.app (.app (.tapp dStepW (.tvar 1)) (.var 5)) (.var 4)) (.var 3))) (.var 0)))
        (.tvar 0)) (.var 2)) (.var 1)))))))))

def pPsiW : FTm :=
  .lam natW (.tlam .star (.lam (lvlW (.tvar 0)) (.lam (.arr (treeSW (.tvar 0)) rTy)
    (.tlam .star (.lam (lvlW (.tvar 0)) (.lam natW
      (.app (.app (.app (.app (.tapp ifLtW (.tvar 0)) (.var 4)) (.var 0))
          (.app (.app (.tapp (.app (.app (.tapp supViaW (.tvar 0)) (.var 1)) (.var 4)) (.tvar 1))
              (.var 3))
            (.app (.app (.app (.tapp (.tapp kkW (.tvar 1)) (.tvar 0)) (.var 2)) (.var 1)) (.var 0))))
        (.app (llimW (.tvar 0))
          (.app (.app (.app (.app (.app (.tapp (.tapp dkW (.tvar 1)) (.tvar 0)) (.var 4)) (.var 3))
            (.var 2)) (.var 1)) (.var 0))))))))))

/-- **Buchholz's collapse at level `ω`**: `TW → ∀E. Lvl E → nat → Tree E`. -/
def psiW : FTm := .lam TWW (app4W (.tapp (.var 0) rTy) omegaOfW sPsiW lPsiW pPsiW)

/-- The Brouwer tree of a tree of level `0`. -/
def toB0W : FTm := trTL (lv4 T0W T0W T0W T0W) (lv4 natW natW natW natW) (TT.toB0T (Γ := []))

/-- **The Takeuti–Feferman–Buchholz ordinal** `ψ_0(ε_{Ω_ω+1})`, as one program. -/
def thetaW : FTm := .app toB0W (.app (.app (.tapp (.app psiW epsTWW) natW) ev0W) zeroW)

end BusyLean.Indep.TFB
