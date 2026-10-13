import BusyLean.SystemFLT.Typing

/-!
# Church-style ladder language (parametric in atoms) and a sound type checker

As for kind-polymorphic Fω, with kind abstraction and application at both
levels; level-0 kind application requires a dyn-free kind.
Type checking needs type equality up to β. `infer fuel` decides it by
comparing fuel-bounded normal forms (`tnf fuel`). The check is *sound*: an
accepted program is typable (`infer_sound`). It may reject typable programs
whose types need more than `fuel` steps to normalize. Contender 8 uses the
syntax budget as fuel, so every program is eventually accepted with enough
fuel.
-/

namespace BusyLean.FLT

open BusyLean.FL

variable {α : Type} [DecidableEq α] [AtomOrder α]

open BusyLean.FT (Tm)
open BusyLean.Fw (nth?)
open Ty

inductive CTm (α : Type) where
  | var : Nat → (CTm α)
  | lam : (Ty α) → (CTm α) → (CTm α)
  | app : (CTm α) → (CTm α) → (CTm α)
  | tlam : (Kind α) → (CTm α) → (CTm α)
  | tapp : (CTm α) → (Ty α) → (CTm α)
  | klam0 : (CTm α) → (CTm α)
  | kapp0 : (CTm α) → (Kind α) → (CTm α)
  | klam1 : (CTm α) → (CTm α)
  | kapp1 : (CTm α) → (Kind α) → (CTm α)
  | orc : (CTm α)

def erase : (CTm α) → Tm
  | .var n => .var n
  | .lam _ b => .lam (erase b)
  | .app t u => .app (erase t) (erase u)
  | .tlam _ b => erase b
  | .tapp t _ => erase t
  | .klam0 t => erase t
  | .kapp0 t _ => erase t
  | .klam1 t => erase t
  | .kapp1 t _ => erase t
  | .orc => .orc

/-- Result type of an application, given the function and argument types. -/
def appResult (fuel : Nat) (T U : (Ty α)) : Option (Ty α) :=
  match tnf fuel T with
  | arr A B => if tnf fuel A = tnf fuel U then some B else none
  | _ => none

/-- Result type of a type application. -/
def tappResult (fuel : Nat) (Δ : List (Kind α)) (T B : (Ty α)) : Option (Ty α) :=
  match tnf fuel T with
  | all k A => if inferKind Δ B = some k then some (Ty.inst A B) else none
  | _ => none

/-- Result type of a level-0 kind application. -/
def kappResult0 (fuel : Nat) (T : (Ty α)) (K : (Kind α)) : Option (Ty α) :=
  match tnf fuel T with
  | kall0 A => if K.dynFree = true then some (Ty.kinst0 A K) else none
  | _ => none

/-- Result type of a level-1 kind application. -/
def kappResult1 (fuel : Nat) (T : (Ty α)) (K : (Kind α)) : Option (Ty α) :=
  match tnf fuel T with
  | kall1 A => some (Ty.kinst1 A K)
  | _ => none

/-- Type inference with `fuel` steps of type normalization per conversion. -/
def infer (fuel : Nat) : List (Kind α) → List (Ty α) → (CTm α) → Option (Ty α)
  | _, Γ, .var n => nth? Γ n
  | Δ, Γ, .lam A b =>
      match inferKind Δ A with
      | some .star => (infer fuel Δ (A :: Γ) b).map (arr A)
      | _ => none
  | Δ, Γ, .app t u =>
      match infer fuel Δ Γ t, infer fuel Δ Γ u with
      | some T, some U => appResult fuel T U
      | _, _ => none
  | Δ, Γ, .tlam k b => (infer fuel (k :: Δ) (Γ.map (tren Nat.succ)) b).map (all k)
  | Δ, Γ, .tapp t B =>
      match infer fuel Δ Γ t with
      | some T => tappResult fuel Δ T B
      | none => none
  | Δ, Γ, .klam0 t =>
      (infer fuel (Δ.map Kind.sh₀) (Γ.map (Ty.kren Nat.succ id)) t).map kall0
  | Δ, Γ, .kapp0 t K =>
      match infer fuel Δ Γ t with
      | some T => kappResult0 fuel T K
      | none => none
  | Δ, Γ, .klam1 t =>
      (infer fuel (Δ.map Kind.sh₁) (Γ.map (Ty.kren id Nat.succ)) t).map kall1
  | Δ, Γ, .kapp1 t K =>
      match infer fuel Δ Γ t with
      | some T => kappResult1 fuel T K
      | none => none
  | _, _, .orc => some (arr Ty.nat Ty.nat)

def ctxOf (Γ : List (Ty α)) : (Ctx α) := fun n => (nth? Γ n).getD Ty.nat

omit [DecidableEq α] [AtomOrder α] in
theorem ctxOf_cons (A : (Ty α)) (Γ : List (Ty α)) : ctxOf (A :: Γ) = Ctx.cons A (ctxOf Γ) := by
  funext n; cases n <;> rfl

omit [DecidableEq α] [AtomOrder α] in
theorem ctxOf_lift (Γ : List (Ty α)) : ctxOf (Γ.map (tren Nat.succ)) = Ctx.lift (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (tren Nat.succ)) n).getD Ty.nat = tren Nat.succ ((nth? Γ n).getD Ty.nat)
  rw [nth?_map]
  cases nth? Γ n <;> rfl

omit [DecidableEq α] [AtomOrder α] in
theorem ctxOf_klift0 (Γ : List (Ty α)) :
    ctxOf (Γ.map (Ty.kren Nat.succ id)) = Ctx.klift0 (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (Ty.kren Nat.succ id)) n).getD Ty.nat =
    Ty.kren Nat.succ id ((nth? Γ n).getD Ty.nat)
  rw [nth?_map]
  cases nth? Γ n <;> rfl

omit [DecidableEq α] [AtomOrder α] in
theorem ctxOf_klift1 (Γ : List (Ty α)) :
    ctxOf (Γ.map (Ty.kren id Nat.succ)) = Ctx.klift1 (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (Ty.kren id Nat.succ)) n).getD Ty.nat =
    Ty.kren id Nat.succ ((nth? Γ n).getD Ty.nat)
  rw [nth?_map]
  cases nth? Γ n <;> rfl

/-- All types in the context have kind `★`. -/
def GoodCtx (Δ : List (Kind α)) (Γ : List (Ty α)) : Prop :=
  ∀ n A, nth? Γ n = some A → Kinded (kctxOf Δ) A .star

omit [DecidableEq α] in
theorem GoodCtx.cons {Δ : List (Kind α)} {Γ : List (Ty α)} (h : GoodCtx Δ Γ) {A : (Ty α)}
    (hA : Kinded (kctxOf Δ) A .star) : GoodCtx Δ (A :: Γ) := fun n B hB => by
  cases n with
  | zero => cases hB; exact hA
  | succ n => exact h n B hB

omit [DecidableEq α] in
theorem GoodCtx.lift {Δ : List (Kind α)} {Γ : List (Ty α)} (h : GoodCtx Δ Γ) (k : (Kind α)) :
    GoodCtx (k :: Δ) (Γ.map (tren Nat.succ)) := fun n B hB => by
  rw [nth?_map] at hB
  cases hn : nth? Γ n with
  | none => rw [hn] at hB; cases hB
  | some A =>
      rw [hn] at hB
      cases hB
      rw [kctxOf_cons]
      exact (h n A hn).ren fun _ => rfl

omit [DecidableEq α] in
theorem GoodCtx.klift0 {Δ : List (Kind α)} {Γ : List (Ty α)} (h : GoodCtx Δ Γ) :
    GoodCtx (Δ.map Kind.sh₀) (Γ.map (Ty.kren Nat.succ id)) := fun n B hB => by
  rw [nth?_map] at hB
  cases hn : nth? Γ n with
  | none => rw [hn] at hB; cases hB
  | some A =>
      rw [hn] at hB
      cases hB
      rw [kctxOf_klift0]
      exact (h n A hn).kren Nat.succ id

omit [DecidableEq α] in
theorem GoodCtx.klift1 {Δ : List (Kind α)} {Γ : List (Ty α)} (h : GoodCtx Δ Γ) :
    GoodCtx (Δ.map Kind.sh₁) (Γ.map (Ty.kren id Nat.succ)) := fun n B hB => by
  rw [nth?_map] at hB
  cases hn : nth? Γ n with
  | none => rw [hn] at hB; cases hB
  | some A =>
      rw [hn] at hB
      cases hB
      rw [kctxOf_klift1]
      exact (h n A hn).kren id Nat.succ

omit [DecidableEq α] in
theorem ctxOf_kinded {Δ : List (Kind α)} {Γ : List (Ty α)} (h : GoodCtx Δ Γ) (n : Nat) :
    Kinded (kctxOf Δ) (ctxOf Γ n) .star := by
  show Kinded _ ((nth? Γ n).getD Ty.nat) _
  cases hn : nth? Γ n with
  | none => exact Kinded.nat _
  | some A => exact h n A hn

theorem appResult_inv {fuel : Nat} {T U A : (Ty α)} (h : appResult fuel T U = some A) :
    ∃ P, TSteps T (arr P A) ∧ TJoin P U := by
  unfold appResult at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  cases N with
  | tvar _ => cases h
  | all _ _ => cases h
  | lam _ _ => cases h
  | app _ _ _ => cases h
  | kall0 _ => cases h
  | kall1 _ => cases h
  | pack _ _ => cases h
  | unpack _ _ => cases h
  | apack _ _ _ => cases h
  | aunpack _ _ _ => cases h
  | arr P Q =>
      change (if tnf fuel P = tnf fuel U then some Q else none) = some A at h
      by_cases e : tnf fuel P = tnf fuel U
      · rw [ite_eq_left e] at h
        cases h
        exact ⟨P, sT, tjoin_of_tnf e⟩
      · rw [ite_eq_right e] at h; cases h

theorem tappResult_inv {fuel : Nat} {Δ : List (Kind α)} {T B A : (Ty α)}
    (h : tappResult fuel Δ T B = some A) :
    ∃ k P, TSteps T (all k P) ∧ inferKind Δ B = some k ∧ A = Ty.inst P B := by
  unfold tappResult at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  cases N with
  | tvar _ => cases h
  | arr _ _ => cases h
  | lam _ _ => cases h
  | app _ _ _ => cases h
  | kall0 _ => cases h
  | kall1 _ => cases h
  | pack _ _ => cases h
  | unpack _ _ => cases h
  | apack _ _ _ => cases h
  | aunpack _ _ _ => cases h
  | all k P =>
      change (if inferKind Δ B = some k then some (Ty.inst P B) else none) = some A at h
      by_cases e : inferKind Δ B = some k
      · rw [ite_eq_left e] at h
        cases h
        exact ⟨k, P, sT, e, rfl⟩
      · rw [ite_eq_right e] at h; cases h

theorem kappResult0_inv {fuel : Nat} {T A : (Ty α)} {K : (Kind α)}
    (h : kappResult0 fuel T K = some A) :
    ∃ P, TSteps T (kall0 P) ∧ K.DynFree ∧ A = Ty.kinst0 P K := by
  unfold kappResult0 at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  cases N with
  | kall0 P =>
      change (if K.dynFree = true then some (Ty.kinst0 P K) else none) = some A at h
      by_cases e : K.dynFree = true
      · rw [ite_eq_left e] at h
        cases h
        exact ⟨P, sT, (Kind.dynFree_iff K).1 e, rfl⟩
      · rw [ite_eq_right e] at h; cases h
  | tvar _ => cases h
  | arr _ _ => cases h
  | all _ _ => cases h
  | lam _ _ => cases h
  | app _ _ _ => cases h
  | kall1 _ => cases h
  | pack _ _ => cases h
  | unpack _ _ => cases h
  | apack _ _ _ => cases h
  | aunpack _ _ _ => cases h

theorem kappResult1_inv {fuel : Nat} {T A : (Ty α)} {K : (Kind α)}
    (h : kappResult1 fuel T K = some A) :
    ∃ P, TSteps T (kall1 P) ∧ A = Ty.kinst1 P K := by
  unfold kappResult1 at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  cases N with
  | kall1 P => cases h; exact ⟨P, sT, rfl⟩
  | tvar _ => cases h
  | arr _ _ => cases h
  | all _ _ => cases h
  | lam _ _ => cases h
  | app _ _ _ => cases h
  | kall0 _ => cases h
  | pack _ _ => cases h
  | unpack _ _ => cases h
  | apack _ _ _ => cases h
  | aunpack _ _ _ => cases h

/-- **Soundness of type checking**: accepted programs are typable, at a kinded type. -/
theorem infer_sound (fuel : Nat) : ∀ (t : (CTm α)) {Δ : List (Kind α)} {Γ : List (Ty α)} {A : (Ty α)},
    GoodCtx Δ Γ → infer fuel Δ Γ t = some A →
      Typed true (kctxOf Δ) (ctxOf Γ) (erase t) A ∧ Kinded (kctxOf Δ) A .star
  | .var n, Δ, Γ, A, hΓ, h => by
      have e : ctxOf Γ n = A := by
        show (nth? Γ n).getD Ty.nat = A
        rw [show nth? Γ n = some A from h]; rfl
      refine ⟨?_, hΓ n A h⟩
      rw [← e]
      exact Typed.var n
  | .lam B b, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hk : inferKind Δ B with
      | none => rw [hk] at h; cases h
      | some k =>
          rw [hk] at h
          cases k with
          | arr _ _ => cases h
          | kvar _ => cases h
          | dvar _ => cases h
          | dyn => cases h
          | atom _ => cases h
          | star =>
              have hB := inferKind_sound B hk
              cases hb : infer fuel Δ (B :: Γ) b with
              | none => rw [hb] at h; cases h
              | some C =>
                  rw [hb] at h
                  cases h
                  obtain ⟨ih, hC⟩ := infer_sound fuel b (hΓ.cons hB) hb
                  rw [ctxOf_cons] at ih
                  exact ⟨Typed.lam ih, Kinded.arr hB hC⟩
  | .app t u, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          cases hu : infer fuel Δ Γ u with
          | none => rw [ht, hu] at h; cases h
          | some U =>
              rw [ht, hu] at h
              obtain ⟨tyT, kT⟩ := infer_sound fuel t hΓ ht
              obtain ⟨tyU, kU⟩ := infer_sound fuel u hΓ hu
              obtain ⟨P, sT, j⟩ := appResult_inv h
              have kPA := kT.steps sT
              cases kPA with
              | arr kP kA =>
                  have t' := Typed.conv tyT kT (Kinded.arr kP kA) sT.join_left
                  have u' := Typed.conv tyU kU kP j.symm
                  exact ⟨Typed.app t' u', kA⟩
  | .tlam k b, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hb : infer fuel (k :: Δ) (Γ.map (tren Nat.succ)) b with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          obtain ⟨ih, hC⟩ := infer_sound fuel b (hΓ.lift k) hb
          rw [kctxOf_cons, ctxOf_lift] at ih
          rw [kctxOf_cons] at hC
          exact ⟨Typed.gen ih, Kinded.all hC⟩
  | .tapp t B, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          obtain ⟨tyT, kT⟩ := infer_sound fuel t hΓ ht
          obtain ⟨k, P, sT, e, rfl⟩ := tappResult_inv h
          have kAll := kT.steps sT
          cases kAll with
          | all kP =>
              have hB := inferKind_sound B e
              have t' := Typed.conv tyT kT (Kinded.all kP) sT.join_left
              exact ⟨Typed.inst B t' kP hB, kP.inst hB⟩
  | .klam0 t, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hb : infer fuel (Δ.map Kind.sh₀) (Γ.map (Ty.kren Nat.succ id)) t with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          obtain ⟨ih, hC⟩ := infer_sound fuel t hΓ.klift0 hb
          rw [kctxOf_klift0, ctxOf_klift0] at ih
          rw [kctxOf_klift0] at hC
          exact ⟨Typed.kgen0 ih, Kinded.kall0 hC⟩
  | .kapp0 t K, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          obtain ⟨tyT, kT⟩ := infer_sound fuel t hΓ ht
          obtain ⟨P, sT, hK, rfl⟩ := kappResult0_inv h
          have kAll := kT.steps sT
          cases kAll with
          | kall0 kP =>
              have t' := Typed.conv tyT kT (Kinded.kall0 kP) sT.join_left
              exact ⟨Typed.kinst0 K t' hK, kP.kinst0 hK⟩
  | .klam1 t, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hb : infer fuel (Δ.map Kind.sh₁) (Γ.map (Ty.kren id Nat.succ)) t with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          obtain ⟨ih, hC⟩ := infer_sound fuel t hΓ.klift1 hb
          rw [kctxOf_klift1, ctxOf_klift1] at ih
          rw [kctxOf_klift1] at hC
          exact ⟨Typed.kgen1 ih, Kinded.kall1 hC⟩
  | .kapp1 t K, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          obtain ⟨tyT, kT⟩ := infer_sound fuel t hΓ ht
          obtain ⟨P, sT, rfl⟩ := kappResult1_inv h
          have kAll := kT.steps sT
          cases kAll with
          | kall1 kP =>
              have t' := Typed.conv tyT kT (Kinded.kall1 kP) sT.join_left
              exact ⟨Typed.kinst1 K t', kP.kinst1 K⟩
  | .orc, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases h
      exact ⟨Typed.orc rfl, Kinded.arr (Kinded.nat _) (Kinded.nat _)⟩

omit [DecidableEq α] in
theorem goodCtx_nil (Δ : List (Kind α)) : GoodCtx Δ [] := fun _ _ h => nomatch h

end BusyLean.FLT
