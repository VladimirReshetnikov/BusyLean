import BusyLean.Independent.TEmbedding
import BusyLean.Independent.Ladder

/-!
# System T as Church-style ladder programs

`trC Γ t` is a Church-style program of the ladder language (System F
fragment: no kinds beyond `★`, no atoms, no oracle) that erases to the untyped
translation `utr Γ t` of `TEmbedding.lean`. Contender 5's types become
`tyT a` (with `nat` the Church numeral type), and natural recursion uses the
polymorphic pair type `∀X. (A → B → X) → X`.

`infer_trC` shows that the ladder's type checker accepts the translation, at
every fuel, with the type `tyT (stype Γ t)`. In particular a closed term of
static type `nat` becomes a closed program of type `nat`.
-/

namespace BusyLean.Indep.Emb

open BusyLean.FL
open BusyLean.Fw (nth?)

variable {α : Type} [DecidableEq α] [AtomOrder α]

/-! ## Types -/

def tyT : C5.Ty → Ty α
  | .nat => Ty.nat
  | .arr a b => .arr (tyT a) (tyT b)

/-- The polymorphic pair type `∀X. (A → B → X) → X`. -/
def pairTyC (A B : Ty α) : Ty α := .all .star (.arr (.arr A (.arr B (.tvar 0))) (.tvar 0))

/-- Closed, normal types of kind `★` in every kind context. -/
structure Good (A : Ty α) : Prop where
  ren : ∀ ξ, Ty.tren ξ A = A
  subst : ∀ σ, Ty.tsubst σ A = A
  nf : tstep A = none
  kind : ∀ Δ : List (Kind α), inferKind Δ A = some .star

theorem Good.arr {A B : Ty α} (hA : Good A) (hB : Good B) : Good (.arr A B) where
  ren ξ := by show Ty.arr (Ty.tren ξ A) (Ty.tren ξ B) = _; rw [hA.ren, hB.ren]
  subst σ := by show Ty.arr (Ty.tsubst σ A) (Ty.tsubst σ B) = _; rw [hA.subst, hB.subst]
  nf := by
    show (match tstep A with
      | some A' => some (Ty.arr A' B)
      | none => (tstep B).map (Ty.arr A)) = none
    rw [hA.nf, hB.nf]; rfl
  kind Δ := by show arrK (inferKind Δ A) (inferKind Δ B) = _; rw [hA.kind, hB.kind]; rfl

theorem good_nat : Good (Ty.nat : Ty α) where
  ren _ := rfl
  subst _ := rfl
  nf := rfl
  kind _ := rfl

theorem good_tyT : ∀ a : C5.Ty, Good (tyT a : Ty α)
  | .nat => good_nat
  | .arr a b => (good_tyT a).arr (good_tyT b)

theorem good_pairTyC {A B : Ty α} (hA : Good A) (hB : Good B) : Good (pairTyC A B) where
  ren ξ := by
    show Ty.all .star (Ty.arr (Ty.arr (Ty.tren _ A) (Ty.arr (Ty.tren _ B) (.tvar _))) (.tvar _)) = _
    rw [hA.ren, hB.ren]; rfl
  subst σ := by
    show Ty.all .star (Ty.arr (Ty.arr (Ty.tsubst _ A) (Ty.arr (Ty.tsubst _ B) _)) _) = _
    rw [hA.subst, hB.subst]; rfl
  nf := by
    show (tstep (Ty.arr (Ty.arr A (Ty.arr B (.tvar 0))) (.tvar 0))).map (Ty.all .star) = none
    have h : tstep (Ty.arr A (Ty.arr B (.tvar 0)) : Ty α) = none := by
      show (match tstep A with
        | some A' => some (Ty.arr A' (Ty.arr B (.tvar 0)))
        | none => (tstep (Ty.arr B (.tvar 0))).map (Ty.arr A)) = none
      rw [hA.nf]
      show (match tstep B with
        | some B' => some (Ty.arr B' (.tvar 0))
        | none => (tstep (.tvar 0 : Ty α)).map (Ty.arr B)).map (Ty.arr A) = none
      rw [hB.nf]; rfl
    show (match tstep (Ty.arr A (Ty.arr B (.tvar 0))) with
      | some A' => some (Ty.arr A' (.tvar 0))
      | none => (tstep (.tvar 0 : Ty α)).map (Ty.arr _)).map (Ty.all .star) = none
    rw [h]; rfl
  kind Δ := by
    show starK (arrK (arrK (inferKind (.star :: Δ) A) (arrK (inferKind (.star :: Δ) B)
      (some .star))) (some .star)) = _
    rw [hA.kind, hB.kind]; rfl

theorem tnf_eq {A : Ty α} (h : tstep A = none) : ∀ fuel, tnf fuel A = A
  | 0 => rfl
  | _ + 1 => by simp only [tnf, h]

/-! ## Inference rules for the System F fragment -/

section Rules

variable {fuel : Nat} {Δ : List (Kind α)} {Γ : List (Ty α)}

theorem infer_var {n : Nat} {A : Ty α} (h : nth? Γ n = some A) :
    infer fuel Δ Γ (.var n) = some A := h

theorem infer_lam {A B : Ty α} {b : CTm α} (hk : inferKind Δ A = some .star)
    (hb : infer fuel Δ (A :: Γ) b = some B) : infer fuel Δ Γ (.lam A b) = some (.arr A B) := by
  show (match inferKind Δ A with
    | some .star => (infer fuel Δ (A :: Γ) b).map (Ty.arr A)
    | _ => none) = _
  rw [hk, hb]; rfl

theorem infer_app {A B : Ty α} {t u : CTm α} (ht : infer fuel Δ Γ t = some (.arr A B))
    (hu : infer fuel Δ Γ u = some A) (hAB : tstep (Ty.arr A B) = none) :
    infer fuel Δ Γ (.app t u) = some B := by
  show (match infer fuel Δ Γ t, infer fuel Δ Γ u with
    | some T, some U => appResult fuel T U
    | _, _ => none) = _
  rw [ht, hu]
  show appResult fuel (Ty.arr A B) A = some B
  unfold appResult
  rw [tnf_eq hAB]
  exact ite_eq_left rfl

theorem infer_tlam {B : Ty α} {b : CTm α}
    (hb : infer fuel (.star :: Δ) (Γ.map (Ty.tren Nat.succ)) b = some B) :
    infer fuel Δ Γ (.tlam .star b) = some (.all .star B) := by
  show (infer fuel (.star :: Δ) (Γ.map (Ty.tren Nat.succ)) b).map (Ty.all .star) = _
  rw [hb]; rfl

theorem infer_tapp {A X : Ty α} {t : CTm α} (ht : infer fuel Δ Γ t = some (.all .star A))
    (hA : tstep (Ty.all .star A) = none) (hX : inferKind Δ X = some .star) :
    infer fuel Δ Γ (.tapp t X) = some (Ty.inst A X) := by
  show (match infer fuel Δ Γ t with
    | some T => tappResult fuel Δ T X
    | none => none) = _
  rw [ht]
  show tappResult fuel Δ (Ty.all .star A) X = _
  unfold tappResult
  rw [tnf_eq hA]
  exact ite_eq_left hX

end Rules

/-! ## Combinators -/

/-- `Λ X. λ s : X → X. λ z : X. z` -/
def zeroC : CTm α := .tlam .star (.lam (.arr (.tvar 0) (.tvar 0)) (.lam (.tvar 0) (.var 0)))

/-- `λ n : nat. Λ X. λ s z. s (n X s z)` -/
def succC : CTm α :=
  .lam Ty.nat (.tlam .star (.lam (.arr (.tvar 0) (.tvar 0)) (.lam (.tvar 0)
    (.app (.var 1) (.app (.app (.tapp (.var 2) (.tvar 0)) (.var 1)) (.var 0))))))

/-- `λ x : A. λ y : B. Λ X. λ k : A → B → X. k x y` -/
def pairC (A B : Ty α) : CTm α :=
  .lam A (.lam B (.tlam .star (.lam (.arr A (.arr B (.tvar 0)))
    (.app (.app (.var 0) (.var 2)) (.var 1)))))

def fstC (A B : Ty α) (p : CTm α) : CTm α := .app (.tapp p A) (.lam A (.lam B (.var 1)))

def sndC (A B : Ty α) (p : CTm α) : CTm α := .app (.tapp p B) (.lam A (.lam B (.var 0)))

/-- `λ g : nat → R → R. λ p. ⟨succ (fst p), g (fst p) (snd p)⟩` -/
def stepC (R : Ty α) : CTm α :=
  .lam (.arr Ty.nat (.arr R R)) (.lam (pairTyC Ty.nat R)
    (.app (.app (pairC Ty.nat R) (.app succC (fstC Ty.nat R (.var 0))))
      (.app (.app (.var 1) (fstC Ty.nat R (.var 0))) (sndC Ty.nat R (.var 0)))))

/-- `λ a : R. λ g : nat → R → R. λ n : nat. snd (n (pair) (step g) ⟨0, a⟩)` -/
def recC (R : Ty α) : CTm α :=
  .lam R (.lam (.arr Ty.nat (.arr R R)) (.lam Ty.nat (sndC Ty.nat R
    (.app (.app (.tapp (.var 0) (pairTyC Ty.nat R)) (.app (stepC R) (.var 1)))
      (.app (.app (pairC Ty.nat R) zeroC) (.var 2))))))

def errC : C5.Ty → CTm α
  | .nat => zeroC
  | .arr a b => .lam (tyT a) (errC b)

def castC (src dst : C5.Ty) (u : CTm α) : CTm α := if C5.typeEqb src dst then u else errC dst

/-- The Church-style translation; it erases to `utr`. -/
def trC (Γ : List C5.Ty) : C5.Term → CTm α
  | .var x =>
      match C5.lookup Γ x with
      | some _ => .var (Γ.length - (x + 1))
      | none => zeroC
  | .lam a b t => .lam (tyT a) (castC (stype (a :: Γ) t) b (trC (a :: Γ) t))
  | .app t u =>
      match stype Γ t with
      | .nat => zeroC
      | .arr a _ => .app (trC Γ t) (castC (stype Γ u) a (trC Γ u))
  | .zero => zeroC
  | .succ => succC
  | .natRec r => recC (tyT r)

/-! ## Erasure -/

omit [DecidableEq α] [AtomOrder α] in
theorem erase_errC : ∀ a : C5.Ty, erase (errC a : CTm α) = errTm a
  | .nat => rfl
  | .arr _ b => congrArg F.Tm.lam (erase_errC b)

omit [DecidableEq α] [AtomOrder α] in
theorem erase_castC (src dst : C5.Ty) (u : CTm α) :
    erase (castC src dst u) = castTm src dst (erase u) := by
  unfold castC castTm
  cases C5.typeEqb src dst
  · exact erase_errC dst
  · rfl

omit [DecidableEq α] [AtomOrder α] in
theorem erase_trC : ∀ (Γ : List C5.Ty) (t : C5.Term), erase (trC Γ t : CTm α) = utr Γ t
  | Γ, .var x => by
      show erase (match C5.lookup Γ x with
        | some _ => (CTm.var (Γ.length - (x + 1)) : CTm α)
        | none => zeroC) = (match C5.lookup Γ x with
        | some _ => F.Tm.var (Γ.length - (x + 1))
        | none => F.Tm.num 0)
      cases C5.lookup Γ x <;> rfl
  | Γ, .lam a b t => by
      show F.Tm.lam (erase (castC _ b (trC (a :: Γ) t : CTm α))) = _
      rw [erase_castC, erase_trC]
      rfl
  | Γ, .app t u => by
      show erase (match stype Γ t with
        | .nat => (zeroC : CTm α)
        | .arr a _ => .app (trC Γ t) (castC (stype Γ u) a (trC Γ u))) = (match stype Γ t with
        | .nat => F.Tm.num 0
        | .arr a _ => F.Tm.app (utr Γ t) (castTm (stype Γ u) a (utr Γ u)))
      cases stype Γ t with
      | nat => rfl
      | arr a _ =>
          show F.Tm.app (erase (trC Γ t : CTm α)) (erase (castC (stype Γ u) a (trC Γ u : CTm α))) = _
          rw [erase_castC, erase_trC, erase_trC]
  | _, .zero => rfl
  | _, .succ => rfl
  | _, .natRec _ => rfl

/-! ## Typing the combinators -/

section Typing

variable {fuel : Nat}

theorem infer_zeroC (Δ : List (Kind α)) (Γ : List (Ty α)) :
    infer fuel Δ Γ zeroC = some Ty.nat :=
  infer_tlam (infer_lam rfl (infer_lam rfl rfl))

theorem infer_succC (Δ : List (Kind α)) (Γ : List (Ty α)) :
    infer fuel Δ Γ succC = some (.arr Ty.nat Ty.nat) := by
  refine infer_lam rfl (infer_tlam (infer_lam rfl (infer_lam rfl ?_)))
  refine infer_app (A := .tvar 0) rfl ?_ rfl
  refine infer_app (A := .tvar 0) ?_ rfl rfl
  refine infer_app (A := .arr (.tvar 0) (.tvar 0)) ?_ rfl rfl
  exact infer_tapp (A := .arr (.arr (.tvar 0) (.tvar 0)) (.arr (.tvar 0) (.tvar 0))) rfl rfl rfl

theorem infer_pairC {A B : Ty α} (hA : Good A) (hB : Good B) (Δ : List (Kind α))
    (Γ : List (Ty α)) : infer fuel Δ Γ (pairC A B) = some (.arr A (.arr B (pairTyC A B))) := by
  refine infer_lam (hA.kind Δ) (infer_lam (hB.kind Δ) (infer_tlam ?_))
  have hK : inferKind (.star :: Δ) (Ty.arr A (Ty.arr B (.tvar 0))) = some .star := by
    show arrK (inferKind _ A) (arrK (inferKind _ B) (some .star)) = _
    rw [hA.kind, hB.kind]; rfl
  refine infer_lam hK ?_
  have hBX : tstep (Ty.arr B (.tvar 0) : Ty α) = none := by
    show (match tstep B with
      | some B' => some (Ty.arr B' (.tvar 0))
      | none => (tstep (.tvar 0 : Ty α)).map (Ty.arr B)) = none
    rw [hB.nf]; rfl
  have hABX : tstep (Ty.arr A (Ty.arr B (.tvar 0)) : Ty α) = none := by
    show (match tstep A with
      | some A' => some (Ty.arr A' (Ty.arr B (.tvar 0)))
      | none => (tstep (Ty.arr B (.tvar 0))).map (Ty.arr A)) = none
    rw [hA.nf, hBX]; rfl
  refine infer_app (A := B) (infer_app (A := A) rfl ?_ hABX) ?_ hBX
  · show some (Ty.tren Nat.succ A) = some A
    rw [hA.ren]
  · show some (Ty.tren Nat.succ B) = some B
    rw [hB.ren]

theorem infer_fstC {A B : Ty α} (hA : Good A) (hB : Good B) {Δ : List (Kind α)}
    {Γ : List (Ty α)} {p : CTm α} (hp : infer fuel Δ Γ p = some (pairTyC A B)) :
    infer fuel Δ Γ (fstC A B p) = some A := by
  have hT : infer fuel Δ Γ (.tapp p A) = some (.arr (.arr A (.arr B A)) A) := by
    have h := infer_tapp hp (good_pairTyC hA hB).nf (hA.kind Δ)
    rw [h]
    show some (Ty.arr (Ty.arr (Ty.tsubst _ A) (Ty.arr (Ty.tsubst _ B) A)) A) = _
    rw [hA.subst, hB.subst]
  have hAB : Good (Ty.arr A (Ty.arr B A)) := hA.arr (hB.arr hA)
  exact infer_app hT (infer_lam (hA.kind Δ) (infer_lam (hB.kind Δ) rfl)) (hAB.arr hA).nf

theorem infer_sndC {A B : Ty α} (hA : Good A) (hB : Good B) {Δ : List (Kind α)}
    {Γ : List (Ty α)} {p : CTm α} (hp : infer fuel Δ Γ p = some (pairTyC A B)) :
    infer fuel Δ Γ (sndC A B p) = some B := by
  have hT : infer fuel Δ Γ (.tapp p B) = some (.arr (.arr A (.arr B B)) B) := by
    have h := infer_tapp hp (good_pairTyC hA hB).nf (hB.kind Δ)
    rw [h]
    show some (Ty.arr (Ty.arr (Ty.tsubst _ A) (Ty.arr (Ty.tsubst _ B) B)) B) = _
    rw [hA.subst, hB.subst]
  have hAB : Good (Ty.arr A (Ty.arr B B)) := hA.arr (hB.arr hB)
  exact infer_app hT (infer_lam (hA.kind Δ) (infer_lam (hB.kind Δ) rfl)) (hAB.arr hB).nf

theorem infer_stepC {R : Ty α} (hR : Good R) (Δ : List (Kind α)) (Γ : List (Ty α)) :
    infer fuel Δ Γ (stepC R) =
      some (.arr (.arr Ty.nat (.arr R R)) (.arr (pairTyC Ty.nat R) (pairTyC Ty.nat R))) := by
  have hN : Good (Ty.nat : Ty α) := good_nat
  have hG : Good (Ty.arr Ty.nat (Ty.arr R R) : Ty α) := hN.arr (hR.arr hR)
  have hP : Good (pairTyC Ty.nat R) := good_pairTyC hN hR
  refine infer_lam (hG.kind Δ) (infer_lam (hP.kind Δ) ?_)
  have hp : infer fuel Δ (pairTyC Ty.nat R :: Ty.arr Ty.nat (Ty.arr R R) :: Γ) (.var 0) =
      some (pairTyC Ty.nat R) := rfl
  have hfst := infer_fstC hN hR hp
  have hsnd := infer_sndC hN hR hp
  refine infer_app (A := R) (infer_app (A := Ty.nat) (infer_pairC hN hR _ _) ?_ ?_) ?_ ?_
  · exact infer_app (infer_succC _ _) hfst rfl
  · exact (hN.arr (hR.arr hP)).nf
  · exact infer_app (A := R) (infer_app (A := Ty.nat) rfl hfst hG.nf) hsnd (hR.arr hR).nf
  · exact (hR.arr hP).nf

theorem infer_recC {R : Ty α} (hR : Good R) (Δ : List (Kind α)) (Γ : List (Ty α)) :
    infer fuel Δ Γ (recC R) =
      some (.arr R (.arr (.arr Ty.nat (.arr R R)) (.arr Ty.nat R))) := by
  have hN : Good (Ty.nat : Ty α) := good_nat
  have hG : Good (Ty.arr Ty.nat (Ty.arr R R) : Ty α) := hN.arr (hR.arr hR)
  have hP : Good (pairTyC Ty.nat R) := good_pairTyC hN hR
  refine infer_lam (hR.kind Δ) (infer_lam (hG.kind Δ) (infer_lam (hN.kind Δ) ?_))
  refine infer_sndC hN hR ?_
  have hn : infer fuel Δ (Ty.nat :: Ty.arr Ty.nat (Ty.arr R R) :: R :: Γ)
      (.tapp (.var 0) (pairTyC Ty.nat R)) =
      some (.arr (.arr (pairTyC Ty.nat R) (pairTyC Ty.nat R))
        (.arr (pairTyC Ty.nat R) (pairTyC Ty.nat R))) :=
    infer_tapp (A := .arr (.arr (.tvar 0) (.tvar 0)) (.arr (.tvar 0) (.tvar 0))) rfl rfl
      (hP.kind Δ)
  refine infer_app (A := pairTyC Ty.nat R)
    (infer_app (A := .arr (pairTyC Ty.nat R) (pairTyC Ty.nat R)) hn ?_ ?_) ?_ ?_
  · exact infer_app (infer_stepC hR _ _) rfl (hG.arr (hP.arr hP)).nf
  · exact ((hP.arr hP).arr (hP.arr hP)).nf
  · exact infer_app (A := R) (infer_app (A := Ty.nat) (infer_pairC hN hR _ _) (infer_zeroC _ _)
      (hN.arr (hR.arr hP)).nf) rfl (hR.arr hP).nf
  · exact (hP.arr hP).nf

theorem infer_errC (Δ : List (Kind α)) : ∀ (a : C5.Ty) (Γ : List (Ty α)),
    infer fuel Δ Γ (errC a) = some (tyT a)
  | .nat, Γ => infer_zeroC Δ Γ
  | .arr a b, _ => infer_lam ((good_tyT a).kind Δ) (infer_errC Δ b _)

theorem infer_castC {Δ : List (Kind α)} {Γ : List (Ty α)} {src : C5.Ty} (dst : C5.Ty) {u : CTm α}
    (hu : infer fuel Δ Γ u = some (tyT src)) :
    infer fuel Δ Γ (castC src dst u) = some (tyT dst) := by
  unfold castC
  cases h : C5.typeEqb src dst with
  | false => exact infer_errC Δ dst Γ
  | true =>
      have e := typeEqb_eq h
      subst e
      exact hu

theorem nth?_map_eq {β γ : Type} (g : β → γ) : ∀ (l : List β) (n : Nat),
    nth? (l.map g) n = (C5.nthError l n).map g
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => nth?_map_eq g l n

theorem infer_trC (Δ : List (Kind α)) : ∀ (Γ : List C5.Ty) (t : C5.Term),
    infer fuel Δ (Γ.map tyT) (trC Γ t) = some (tyT (stype Γ t))
  | Γ, .var x => by
      show infer fuel Δ (Γ.map tyT) (match C5.lookup Γ x with
          | some _ => .var (Γ.length - (x + 1))
          | none => zeroC) = some (tyT (match C5.lookup Γ x with
          | some a => a
          | none => .nat))
      cases hl : C5.lookup Γ x with
      | none => exact infer_zeroC Δ _
      | some a =>
          show nth? (Γ.map tyT) (Γ.length - (x + 1)) = some (tyT a)
          rw [nth?_map_eq, lookup_some hl]
          rfl
  | Γ, .lam a b t => by
      refine infer_lam ((good_tyT a).kind Δ) ?_
      exact infer_castC b (infer_trC Δ (a :: Γ) t)
  | Γ, .app t u => by
      have iht := infer_trC Δ Γ t
      show infer fuel Δ (Γ.map tyT) (match stype Γ t with
          | .nat => zeroC
          | .arr a _ => .app (trC Γ t) (castC (stype Γ u) a (trC Γ u))) =
        some (tyT (match stype Γ t with
          | .nat => .nat
          | .arr _ b => b))
      revert iht
      cases stype Γ t with
      | nat => intro _; exact infer_zeroC Δ _
      | arr a b =>
          intro iht
          exact infer_app iht (infer_castC a (infer_trC Δ Γ u))
            ((good_tyT a).arr (good_tyT b)).nf
  | _, .zero => infer_zeroC Δ _
  | _, .succ => infer_succC Δ _
  | Γ, .natRec r => infer_recC (good_tyT r) Δ (Γ.map tyT)

end Typing

end BusyLean.Indep.Emb
