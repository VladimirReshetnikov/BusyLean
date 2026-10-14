import BusyLean.Independent.TreeEmbedding
import BusyLean.Independent.SystemFCheck

/-!
# Buchholz's ordinal `ψ_0(Ω_ω)` as one ladder program (proof infrastructure)

The trees of level `K` have a Church type that depends on `K`, so no fixed
simply typed program reaches every level. System F does: an **impredicative
existential package**

  `E = ∀R. (∀P. nat → (P → Tree P) → (Tree P → P) → R) → R`

hides the type `P` of the trees of level `K` together with `K`, the lifting
`P → Tree P` and the projection `Tree P → P`. One step builds the package of
level `K + 1` (`stepPF`), and the Church numeral `K` iterates it from the
package of level `0` (`pkg0F`). The body `bodyF`, polymorphic in `P`, computes
`ψ_0(ε_{Ω_{K+2}+1})` from the operations of level `K`. So

  `thetaF = λK. K [E] stepPF pkg0F [tree] bodyF : nat → tree`

computes the whole family whose limit is `ψ_0(Ω_ω)`.

* **Typing** is checked by the kernel with the verified checker of
  `SystemFCheck.lean` (`check_thetaF`).
* **Semantics** (`rel_thetaF`) reuses the logical relation of the tree
  language at each level: the pieces of `thetaF` are translations of closed
  `TT` terms whose untyped form does not depend on the level.
-/

namespace BusyLean.Indep.Omega

open BusyLean.Indep.SF
open BusyLean.Indep.TT (Rel RelLS RelP EnvRel utrT rel_utrT)
open BusyLean.F (Steps)

/-! ## Types -/

def tXF : FTy := .tvar 0
def tXXF : FTy := .arr tXF tXF
def natF : FTy := .all (.arr (.arr (.tvar 0) (.tvar 0)) (.arr (.tvar 0) (.tvar 0)))
def tLF : FTy := .arr (.arr natF tXF) tXF
/-- Brouwer trees. -/
def treeF : FTy := .all (.arr tXF (.arr tXXF (.arr tLF tXF)))
/-- The handler of `sup` nodes branching over `E`. -/
def tPDF (E : FTy) : FTy := .arr natF (.arr (.arr E tXF) tXF)
/-- Trees branching over `D` (`D` may mention outer type variables). -/
def treeS (D : FTy) : FTy := .all (.arr tXF (.arr tXXF (.arr tLF (.arr (tPDF (D.ren Nat.succ)) tXF))))
def pairTyF (A B : FTy) : FTy := .all (.arr (.arr (A.ren Nat.succ) (.arr (B.ren Nat.succ) tXF)) tXF)

/-! ## Typed combinators (open types are shifted under type binders) -/

def app3F (u z s l : FTm) : FTm := .app (.app (.app u z) s) l
def app4F (u z s l p : FTm) : FTm := .app (app3F u z s l) p

def zeroF : FTm := .tlam (.lam tXXF (.lam tXF (.var 0)))

def succF : FTm :=
  .lam natF (.tlam (.lam tXXF (.lam tXF
    (.app (.var 1) (.app (.app (.tapp (.var 2) tXF) (.var 1)) (.var 0))))))

def pairTmF (A B : FTy) : FTm :=
  .lam A (.lam B (.tlam (.lam (.arr (A.ren Nat.succ) (.arr (B.ren Nat.succ) tXF))
    (.app (.app (.var 0) (.var 2)) (.var 1)))))

def fstF (A B : FTy) (p : FTm) : FTm := .app (.tapp p A) (.lam A (.lam B (.var 1)))

def sndF (A B : FTy) (p : FTm) : FTm := .app (.tapp p B) (.lam A (.lam B (.var 0)))

def stepF (R : FTy) : FTm :=
  .lam (.arr natF (.arr R R)) (.lam (pairTyF natF R)
    (.app (.app (pairTmF natF R) (.app succF (fstF natF R (.var 0))))
      (.app (.app (.var 1) (fstF natF R (.var 0))) (sndF natF R (.var 0)))))

def recF (R : FTy) : FTm :=
  .lam R (.lam (.arr natF (.arr R R)) (.lam natF (sndF natF R
    (.app (.app (.tapp (.var 0) (pairTyF natF R)) (.app (stepF R) (.var 1)))
      (.app (.app (pairTmF natF R) zeroF) (.var 2))))))

def tzeroF : FTm := .tlam (.lam tXF (.lam tXXF (.lam tLF (.var 2))))

def tsuccF : FTm :=
  .lam treeF (.tlam (.lam tXF (.lam tXXF (.lam tLF
    (.app (.var 1) (app3F (.tapp (.var 3) tXF) (.var 2) (.var 1) (.var 0)))))))

def tlimF : FTm :=
  .lam (.arr natF treeF) (.tlam (.lam tXF (.lam tXXF (.lam tLF
    (.app (.var 0) (.lam natF (app3F (.tapp (.app (.var 4) (.var 0)) tXF) (.var 3) (.var 2) (.var 1))))))))

def foldF (R : FTy) : FTm :=
  .lam R (.lam (.arr R R) (.lam (.arr (.arr natF R) R) (.lam treeF
    (app3F (.tapp (.var 0) R) (.var 3) (.var 2) (.var 1)))))

def lzeroF (D : FTy) : FTm :=
  .tlam (.lam tXF (.lam tXXF (.lam tLF (.lam (tPDF (D.ren Nat.succ)) (.var 3)))))

def lsuccF (D : FTy) : FTm :=
  .lam (treeS D) (.tlam (.lam tXF (.lam tXXF (.lam tLF (.lam (tPDF (D.ren Nat.succ))
    (.app (.var 2) (app4F (.tapp (.var 4) tXF) (.var 3) (.var 2) (.var 1) (.var 0))))))))

def llimF (D : FTy) : FTm :=
  .lam (.arr natF (treeS D)) (.tlam (.lam tXF (.lam tXXF (.lam tLF (.lam (tPDF (D.ren Nat.succ))
    (.app (.var 1) (.lam natF
      (app4F (.tapp (.app (.var 5) (.var 0)) tXF) (.var 4) (.var 3) (.var 2) (.var 1)))))))))

def lsupF (D : FTy) : FTm :=
  .lam natF (.lam (.arr D (treeS D)) (.tlam (.lam tXF (.lam tXXF (.lam tLF
    (.lam (tPDF (D.ren Nat.succ)) (.app (.app (.var 0) (.var 5)) (.lam (D.ren Nat.succ)
      (app4F (.tapp (.app (.var 5) (.var 0)) tXF) (.var 4) (.var 3) (.var 2) (.var 1))))))))))

def lfoldF (D R : FTy) : FTm :=
  .lam R (.lam (.arr R R) (.lam (.arr (.arr natF R) R)
    (.lam (.arr natF (.arr (.arr D R) R)) (.lam (treeS D)
      (app4F (.tapp (.var 0) R) (.var 4) (.var 3) (.var 2) (.var 1))))))

/-! ## The typed translation of `TT`, relative to a base type `b` for level `0` -/

/-- The type of level `m` over the base `b`. -/
def levF (b : FTy) : Nat → FTy
  | 0 => b
  | m + 1 => treeS (levF b m)

def tyTF (b : FTy) : TT.Ty → FTy
  | .nat => natF
  | .tree => treeF
  | .lev m => levF b m
  | .arr a c => .arr (tyTF b a) (tyTF b c)

/-- The branching type of level `m` (`bd` at level `0`). -/
def domF (b bd : FTy) : Nat → FTy
  | 0 => bd
  | m + 1 => levF b m

def trTF (b bd : FTy) : {Γ : List TT.Ty} → {σ : TT.Ty} → TT.Tm Γ σ → FTm
  | _, _, .var v => .var v.idx
  | _, _, @TT.Tm.lam _ a _ t => .lam (tyTF b a) (trTF b bd t)
  | _, _, .app s u => .app (trTF b bd s) (trTF b bd u)
  | _, _, .zero => zeroF
  | _, _, .succ => succF
  | _, _, .nrec r => recF (tyTF b r)
  | _, _, .tzero => tzeroF
  | _, _, .tsucc => tsuccF
  | _, _, .tlim => tlimF
  | _, _, .fold r => foldF (tyTF b r)
  | _, _, .lzero m => lzeroF (domF b bd m)
  | _, _, .lsucc m => lsuccF (domF b bd m)
  | _, _, .llim m => llimF (domF b bd m)
  | _, _, .lsup m => lsupF (levF b m)
  | _, _, .lfold0 r => lfoldF bd (tyTF b r)
  | _, _, .lfoldS m r => lfoldF (levF b m) (tyTF b r)

theorem eraseF_trTF (b bd : FTy) : ∀ {Γ : List TT.Ty} {σ : TT.Ty} (t : TT.Tm Γ σ),
    eraseF (trTF b bd t) = utrT t
  | _, _, .var _ => rfl
  | _, _, .lam t => congrArg F.Tm.lam (eraseF_trTF b bd t)
  | _, _, .app s u => by
      show F.Tm.app (eraseF (trTF b bd s)) (eraseF (trTF b bd u)) = _
      rw [eraseF_trTF b bd s, eraseF_trTF b bd u]; rfl
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
  | _, _, .lfold0 _ => rfl
  | _, _, .lfoldS _ _ => rfl

/-! ## The program -/

/-- The continuation type `∀P. nat → (P → Tree P) → (Tree P → P) → R`, with `R = tvar 0`. -/
def CtyF : FTy :=
  .all (.arr natF (.arr (.arr (.tvar 0) (treeS (.tvar 0)))
    (.arr (.arr (treeS (.tvar 0)) (.tvar 0)) (.tvar 1))))

/-- Packages: `∃P. nat × (P → Tree P) × (Tree P → P)`, impredicatively. -/
def EF : FTy := .all (.arr CtyF (.tvar 0))

/-- The trees of level `0`. -/
def b0F : FTy := treeS natF

/-- The package of level `0`. -/
def pkg0F : FTm :=
  .tlam (.lam CtyF (.app (.app (.app (.tapp (.var 0) b0F) zeroF)
    (trTF b0F natF (TT.lift0T (Γ := [])))) (trTF b0F natF (TT.proj0T (Γ := [])))))

def liftF : FTm := trTF (.tvar 0) natF (TT.liftStepT 0 (Γ := []))
def projF : FTm := trTF (.tvar 0) natF (TT.projStepT 0 (Γ := []))

/-- The step from the package of level `K` to the package of level `K + 1`. -/
def stepPF : FTm :=
  .lam EF (.tlam (.lam CtyF (.app (.tapp (.var 1) (.tvar 0))
    (.tlam (.lam natF (.lam (.arr (.tvar 0) (treeS (.tvar 0)))
      (.lam (.arr (treeS (.tvar 0)) (.tvar 0))
        (.app (.app (.app (.tapp (.var 3) (treeS (.tvar 0))) (.app succF (.var 2)))
          (.app (.app liftF (.var 2)) (.var 0)))
          (.app (.app projF (.var 2)) (.var 1))))))))))

/-- `ΛP. λ j l p. ψ_0(ε_{Ω_{j+2}+1})`. -/
def bodyF : FTm := .tlam (trTF (.tvar 0) natF (TT.thetaBodyT 0 (Γ := [])))

/-- **The family `K ↦ ψ_0(ε_{Ω_{K+2}+1})` as one program.** -/
def thetaF : FTm :=
  .lam natF (.app (.tapp (.app (.app (.tapp (.var 0) EF) stepPF) pkg0F) treeF) bodyF)

theorem check_thetaF : checkF 0 [] thetaF = some (.arr natF treeF) := by decide +kernel


/-! ## Closed untyped terms -/

open BusyLean.F.Tm (var app lam ren subst cons up num)

/-- All free variables are `< k`. -/
def closedB : Nat → F.Tm → Bool
  | k, .var n => decide (n < k)
  | k, .app t u => closedB k t && closedB k u
  | k, .lam t => closedB (k + 1) t
  | _, .orc => true

theorem subst_closedB : ∀ (t : F.Tm) {k : Nat} {σ : Nat → F.Tm}, closedB k t = true →
    (∀ i, i < k → σ i = .var i) → subst σ t = t
  | .var n, _, _, h, hσ => hσ n (of_decide_eq_true h)
  | .app t u, k, σ, h, hσ => by
      have h' : closedB k t = true ∧ closedB k u = true := by
        simp only [closedB, Bool.and_eq_true] at h; exact h
      show F.Tm.app (subst σ t) (subst σ u) = _
      rw [subst_closedB t h'.1 hσ, subst_closedB u h'.2 hσ]
  | .lam t, k, σ, h, hσ => by
      have hup : ∀ i, i < k + 1 → up σ i = .var i := fun i hi => by
        cases i with
        | zero => rfl
        | succ i =>
            show ren Nat.succ (σ i) = _
            rw [hσ i (Nat.lt_of_succ_lt_succ hi)]
            rfl
      show F.Tm.lam (subst (up σ) t) = _
      rw [subst_closedB t (k := k + 1) h hup]
  | .orc, _, _, _, _ => rfl

theorem subst_closed {t : F.Tm} (h : closedB 0 t = true) (σ : Nat → F.Tm) : subst σ t = t :=
  subst_closedB t h (fun i hi => absurd hi (Nat.not_lt_zero i))

/-! ## The untyped program -/

def LIFTU : F.Tm := utrT (TT.liftStepT 0 (Γ := []))
def PROJU : F.Tm := utrT (TT.projStepT 0 (Γ := []))
def BODYU : F.Tm := utrT (TT.thetaBodyT 0 (Γ := []))
def L0U : F.Tm := utrT (TT.lift0T (Γ := []))
def P0U : F.Tm := utrT (TT.proj0T (Γ := []))

/-- The body of the step, under `e c j l p`. -/
def stepBodyU : F.Tm :=
  app (app (app (var 3) (app Emb.succTm (var 2))) (app (app LIFTU (var 2)) (var 0)))
    (app (app PROJU (var 2)) (var 1))

def STEPU : F.Tm := lam (lam (app (var 1) (lam (lam (lam stepBodyU)))))

def PKG0U : F.Tm := lam (app (app (app (var 0) (num 0)) L0U) P0U)

theorem eraseF_thetaF :
    eraseF thetaF = lam (app (app (app (var 0) STEPU) PKG0U) BODYU) := by
  have e1 : eraseF liftF = LIFTU := eraseF_trTF _ _ _
  have e2 : eraseF projF = PROJU := eraseF_trTF _ _ _
  have e3 : eraseF (trTF b0F natF (TT.lift0T (Γ := []))) = L0U := eraseF_trTF _ _ _
  have e4 : eraseF (trTF b0F natF (TT.proj0T (Γ := []))) = P0U := eraseF_trTF _ _ _
  have e5 : eraseF (trTF (.tvar 0) natF (TT.thetaBodyT 0 (Γ := []))) = BODYU := eraseF_trTF _ _ _
  show lam (app (app (app (var 0)
      (lam (lam (app (var 1) (lam (lam (lam (app (app (app (var 3) (app (eraseF succF) (var 2)))
        (app (app (eraseF liftF) (var 2)) (var 0))) (app (app (eraseF projF) (var 2)) (var 1))))))))))
      (lam (app (app (app (var 0) (eraseF zeroF)) (eraseF (trTF b0F natF (TT.lift0T (Γ := [])))))
        (eraseF (trTF b0F natF (TT.proj0T (Γ := [])))))))
      (eraseF (trTF (.tvar 0) natF (TT.thetaBodyT 0 (Γ := []))))) = _
  rw [e1, e2, e3, e4, e5]
  rfl

theorem closed_LIFTU : closedB 0 LIFTU = true := by decide +kernel
theorem closed_PROJU : closedB 0 PROJU = true := by decide +kernel
theorem closed_BODYU : closedB 0 BODYU = true := by decide +kernel
theorem closed_L0U : closedB 0 L0U = true := by decide +kernel
theorem closed_P0U : closedB 0 P0U = true := by decide +kernel
theorem closed_succTm : closedB 0 Emb.succTm = true := by decide +kernel
theorem closed_STEPU : closedB 0 STEPU = true := by decide +kernel
theorem closed_PKG0U : closedB 0 PKG0U = true := by decide +kernel

/-! ## Semantics -/

variable {f : Nat → Nat}

/-- The untyped translation of a closed `TT` term represents its value. -/
theorem rel_utrT0 {σ : TT.Ty} (t : TT.Tm [] σ) : Rel f σ (utrT t) (TT.eval t TT.env0) := by
  have h := rel_utrT (f := f) t (σs := var) (ρ := TT.env0) (fun _ v => nomatch v)
  rwa [F.Tm.subst_var] at h

/-- `u` is (up to reduction) the package of level `K`. -/
def Pkg (f : Nat → Nat) (u : F.Tm) (K : Nat) : Prop :=
  ∀ c, ∃ L P, Rel f (.arr (.lev K) (.lev (K + 1))) L (Buch.lift K) ∧
    Rel f (.arr (.lev (K + 1)) (.lev K)) P (Buch.proj K) ∧
    Steps f (app u c) (app (app (app c (num K)) L) P)

theorem pkg0 : Pkg f PKG0U 0 := by
  intro c
  refine ⟨L0U, P0U, ?_, ?_, ?_⟩
  · have h := rel_utrT0 (f := f) (TT.lift0T (Γ := []))
    rw [TT.eval_lift0T] at h
    exact h
  · have h := rel_utrT0 (f := f) (TT.proj0T (Γ := []))
    rw [TT.eval_proj0T] at h
    exact h
  · have h := F.Steps.beta (f := f) (app (app (app (var 0) (num 0)) L0U) P0U) c
    have e : subst (cons c var) (app (app (app (var 0) (num 0)) L0U) P0U) =
        app (app (app c (subst (cons c var) (num 0))) (subst (cons c var) L0U))
          (subst (cons c var) P0U) := rfl
    rw [e, F.Tm.subst_num, subst_closed closed_L0U, subst_closed closed_P0U] at h
    exact h

theorem subst_ren3 (c : F.Tm) (a b d : F.Tm) :
    subst (cons a (cons b (cons d var))) (ren Nat.succ (ren Nat.succ (ren Nat.succ c))) = c := by
  rw [F.Tm.subst_ren, F.Tm.subst_ren, F.Tm.subst_ren]
  exact F.Tm.subst_var c

theorem pkgStep {u : F.Tm} {K : Nat} (hu : Pkg f u K) : Pkg f (app STEPU u) (K + 1) := by
  intro c
  let B' : F.Tm := app (app (app (ren Nat.succ (ren Nat.succ (ren Nat.succ c)))
      (app Emb.succTm (var 2))) (app (app LIFTU (var 2)) (var 0))) (app (app PROJU (var 2)) (var 1))
  have h1 : Steps f (app (app STEPU u) c) (app u (lam (lam (lam B')))) := by
    have h := Emb.steps_beta2 (f := f) (app (var 1) (lam (lam (lam stepBodyU)))) u c
    have e : subst (cons c (cons u var)) (app (var 1) (lam (lam (lam stepBodyU)))) =
        app u (lam (lam (lam (app (app (app (ren Nat.succ (ren Nat.succ (ren Nat.succ c)))
          (app (subst (up (up (up (cons c (cons u var))))) Emb.succTm) (var 2)))
          (app (app (subst (up (up (up (cons c (cons u var))))) LIFTU) (var 2)) (var 0)))
          (app (app (subst (up (up (up (cons c (cons u var))))) PROJU) (var 2)) (var 1)))))) := rfl
    rw [e, subst_closed closed_succTm, subst_closed closed_LIFTU, subst_closed closed_PROJU] at h
    exact h
  obtain ⟨L, P, hL, hP, h2⟩ := hu (lam (lam (lam B')))
  have h3 : Steps f (app (app (app (lam (lam (lam B'))) (num K)) L) P)
      (app (app (app c (app Emb.succTm (num K))) (app (app LIFTU (num K)) P))
        (app (app PROJU (num K)) L)) := by
    have h := Emb.steps_beta3 (f := f) B' (num K) L P
    have e : subst (cons P (cons L (cons (num K) var))) B' =
        app (app (app (subst (cons P (cons L (cons (num K) var)))
            (ren Nat.succ (ren Nat.succ (ren Nat.succ c))))
          (app (subst (cons P (cons L (cons (num K) var))) Emb.succTm) (num K)))
          (app (app (subst (cons P (cons L (cons (num K) var))) LIFTU) (num K)) P))
          (app (app (subst (cons P (cons L (cons (num K) var))) PROJU) (num K)) L) := rfl
    rw [e, subst_ren3, subst_closed closed_succTm, subst_closed closed_LIFTU,
      subst_closed closed_PROJU] at h
    exact h
  have hsucc : Steps f (app Emb.succTm (num K)) (num (K + 1)) :=
    TT.rel_succ (f := f) (num K) K (F.Steps.refl _)
  have h4 : Steps f (app (app (app c (app Emb.succTm (num K))) (app (app LIFTU (num K)) P))
        (app (app PROJU (num K)) L))
      (app (app (app c (num (K + 1))) (app (app LIFTU (num K)) P)) (app (app PROJU (num K)) L)) :=
    F.Steps.appL _ (F.Steps.appL _ (F.Steps.appR c hsucc))
  refine ⟨app (app LIFTU (num K)) P, app (app PROJU (num K)) L, ?_, ?_,
    h1.trans ((h2).trans (h3.trans h4))⟩
  · have h := rel_utrT0 (f := f) (TT.liftStepT K (Γ := []))
    have e : utrT (TT.liftStepT K (Γ := [])) = LIFTU := rfl
    rw [e] at h
    have h' := h (num K) K (F.Steps.refl _) P (Buch.proj K) hP
    rw [TT.eval_liftStepT] at h'
    exact h'
  · have h := rel_utrT0 (f := f) (TT.projStepT K (Γ := []))
    have e : utrT (TT.projStepT K (Γ := [])) = PROJU := rfl
    rw [e] at h
    have h' := h (num K) K (F.Steps.refl _) L (Buch.lift K) hL
    rw [TT.eval_projStepT] at h'
    exact h'

theorem pkgIter : ∀ K, Pkg f (Emb.iterTm STEPU PKG0U K) K
  | 0 => pkg0
  | K + 1 => pkgStep (pkgIter K)

/-- **The program represents the family `K ↦ ψ_0(ε_{Ω_{K+2}+1})`.** -/
theorem rel_thetaF : Rel f (.arr .nat .tree) (eraseF thetaF) (fun K => Buch.theta (K + 1)) := by
  rw [eraseF_thetaF]
  intro w K hw
  have h1 : Steps f (app (lam (app (app (app (var 0) STEPU) PKG0U) BODYU)) w)
      (app (app (app w STEPU) PKG0U) BODYU) := by
    have h := F.Steps.beta (f := f) (app (app (app (var 0) STEPU) PKG0U) BODYU) w
    have e : subst (cons w var) (app (app (app (var 0) STEPU) PKG0U) BODYU) =
        app (app (app w (subst (cons w var) STEPU)) (subst (cons w var) PKG0U))
          (subst (cons w var) BODYU) := rfl
    rw [e, subst_closed closed_STEPU, subst_closed closed_PKG0U, subst_closed closed_BODYU] at h
    exact h
  have h2 : Steps f (app (app (app w STEPU) PKG0U) BODYU)
      (app (app (app (num K) STEPU) PKG0U) BODYU) :=
    F.Steps.appL _ (F.Steps.appL _ (F.Steps.appL _ hw))
  have h3 : Steps f (app (app (app (num K) STEPU) PKG0U) BODYU)
      (app (Emb.iterTm STEPU PKG0U K) BODYU) :=
    F.Steps.appL _ (Emb.steps_num_app K STEPU PKG0U)
  obtain ⟨L, P, hL, hP, h4⟩ := pkgIter (f := f) K BODYU
  have hB := rel_utrT0 (f := f) (TT.thetaBodyT K (Γ := []))
  have e : utrT (TT.thetaBodyT K (Γ := [])) = BODYU := rfl
  rw [e] at hB
  have hR := hB (num K) K (F.Steps.refl _) L (Buch.lift K) hL P (Buch.proj K) hP
  rw [TT.eval_thetaBodyT_level] at hR
  exact TT.RelT.expand (h1.trans (h2.trans (h3.trans h4))) hR

theorem cdepth_thetaF : cdepthF thetaF ≤ 100 := by decide +kernel

end BusyLean.Indep.Omega
