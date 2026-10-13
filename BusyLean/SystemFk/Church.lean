import BusyLean.SystemFk.Typing

/-!
# Church-style kind-polymorphic System Fω and a sound type checker

As for Fω, plus kind abstraction `klam` and kind application `kapp`.
Type checking needs type equality up to β. `infer fuel` decides it by
comparing fuel-bounded normal forms (`tnf fuel`). The check is *sound*: an
accepted program is typable (`infer_sound`). It may reject typable programs
whose types need more than `fuel` steps to normalize. Contender 8 uses the
syntax budget as fuel, so every program is eventually accepted with enough
fuel.
-/

namespace BusyLean.Fk

open BusyLean.F (Tm)
open BusyLean.Fw (nth?)
open Ty

inductive CTm where
  | var : Nat → CTm
  | lam : Ty → CTm → CTm
  | app : CTm → CTm → CTm
  | tlam : Kind → CTm → CTm
  | tapp : CTm → Ty → CTm
  | klam : CTm → CTm
  | kapp : CTm → Kind → CTm
  | orc : CTm

def erase : CTm → Tm
  | .var n => .var n
  | .lam _ b => .lam (erase b)
  | .app t u => .app (erase t) (erase u)
  | .tlam _ b => erase b
  | .tapp t _ => erase t
  | .klam t => erase t
  | .kapp t _ => erase t
  | .orc => .orc

/-- Result type of an application, given the function and argument types. -/
def appResult (fuel : Nat) (T U : Ty) : Option Ty :=
  match tnf fuel T with
  | arr A B => if tnf fuel A = tnf fuel U then some B else none
  | _ => none

/-- Result type of a type application. -/
def tappResult (fuel : Nat) (Δ : List Kind) (T B : Ty) : Option Ty :=
  match tnf fuel T with
  | all k A => if inferKind Δ B = some k then some (Ty.inst A B) else none
  | _ => none

/-- Result type of a kind application. -/
def kappResult (fuel : Nat) (T : Ty) (K : Kind) : Option Ty :=
  match tnf fuel T with
  | kall A => some (Ty.kinst A K)
  | _ => none

/-- Type inference with `fuel` steps of type normalization per conversion. -/
def infer (fuel : Nat) : List Kind → List Ty → CTm → Option Ty
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
  | Δ, Γ, .klam t =>
      (infer fuel (Δ.map (Kind.kren Nat.succ)) (Γ.map (Ty.kren Nat.succ)) t).map kall
  | Δ, Γ, .kapp t K =>
      match infer fuel Δ Γ t with
      | some T => kappResult fuel T K
      | none => none
  | _, _, .orc => some (arr Ty.nat Ty.nat)

def ctxOf (Γ : List Ty) : Ctx := fun n => (nth? Γ n).getD Ty.nat

theorem ctxOf_cons (A : Ty) (Γ : List Ty) : ctxOf (A :: Γ) = Ctx.cons A (ctxOf Γ) := by
  funext n; cases n <;> rfl

theorem ctxOf_lift (Γ : List Ty) : ctxOf (Γ.map (tren Nat.succ)) = Ctx.lift (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (tren Nat.succ)) n).getD Ty.nat = tren Nat.succ ((nth? Γ n).getD Ty.nat)
  rw [nth?_map]
  cases nth? Γ n <;> rfl

theorem ctxOf_klift (Γ : List Ty) :
    ctxOf (Γ.map (Ty.kren Nat.succ)) = Ctx.klift (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (Ty.kren Nat.succ)) n).getD Ty.nat =
    Ty.kren Nat.succ ((nth? Γ n).getD Ty.nat)
  rw [nth?_map]
  cases nth? Γ n <;> rfl

/-- All types in the context have kind `★`. -/
def GoodCtx (Δ : List Kind) (Γ : List Ty) : Prop :=
  ∀ n A, nth? Γ n = some A → Kinded (kctxOf Δ) A .star

theorem GoodCtx.cons {Δ : List Kind} {Γ : List Ty} (h : GoodCtx Δ Γ) {A : Ty}
    (hA : Kinded (kctxOf Δ) A .star) : GoodCtx Δ (A :: Γ) := fun n B hB => by
  cases n with
  | zero => cases hB; exact hA
  | succ n => exact h n B hB

theorem GoodCtx.lift {Δ : List Kind} {Γ : List Ty} (h : GoodCtx Δ Γ) (k : Kind) :
    GoodCtx (k :: Δ) (Γ.map (tren Nat.succ)) := fun n B hB => by
  rw [nth?_map] at hB
  cases hn : nth? Γ n with
  | none => rw [hn] at hB; cases hB
  | some A =>
      rw [hn] at hB
      cases hB
      rw [kctxOf_cons]
      exact (h n A hn).ren fun _ => rfl

theorem GoodCtx.klift {Δ : List Kind} {Γ : List Ty} (h : GoodCtx Δ Γ) :
    GoodCtx (Δ.map (Kind.kren Nat.succ)) (Γ.map (Ty.kren Nat.succ)) := fun n B hB => by
  rw [nth?_map] at hB
  cases hn : nth? Γ n with
  | none => rw [hn] at hB; cases hB
  | some A =>
      rw [hn] at hB
      cases hB
      rw [kctxOf_klift]
      exact (h n A hn).kren Nat.succ

theorem ctxOf_kinded {Δ : List Kind} {Γ : List Ty} (h : GoodCtx Δ Γ) (n : Nat) :
    Kinded (kctxOf Δ) (ctxOf Γ n) .star := by
  show Kinded _ ((nth? Γ n).getD Ty.nat) _
  cases hn : nth? Γ n with
  | none => exact Kinded.nat _
  | some A => exact h n A hn

theorem appResult_inv {fuel : Nat} {T U A : Ty} (h : appResult fuel T U = some A) :
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
  | kall _ => cases h
  | arr P Q =>
      change (if tnf fuel P = tnf fuel U then some Q else none) = some A at h
      by_cases e : tnf fuel P = tnf fuel U
      · rw [ite_eq_left e] at h
        cases h
        exact ⟨P, sT, tjoin_of_tnf e⟩
      · rw [ite_eq_right e] at h; cases h

theorem tappResult_inv {fuel : Nat} {Δ : List Kind} {T B A : Ty}
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
  | kall _ => cases h
  | all k P =>
      change (if inferKind Δ B = some k then some (Ty.inst P B) else none) = some A at h
      by_cases e : inferKind Δ B = some k
      · rw [ite_eq_left e] at h
        cases h
        exact ⟨k, P, sT, e, rfl⟩
      · rw [ite_eq_right e] at h; cases h

theorem kappResult_inv {fuel : Nat} {T A : Ty} {K : Kind} (h : kappResult fuel T K = some A) :
    ∃ P, TSteps T (kall P) ∧ A = Ty.kinst P K := by
  unfold kappResult at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  cases N with
  | kall P => cases h; exact ⟨P, sT, rfl⟩
  | tvar _ => cases h
  | arr _ _ => cases h
  | all _ _ => cases h
  | lam _ _ => cases h
  | app _ _ _ => cases h

/-- **Soundness of type checking**: accepted programs are typable, at a kinded type. -/
theorem infer_sound (fuel : Nat) : ∀ (t : CTm) {Δ : List Kind} {Γ : List Ty} {A : Ty},
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
  | .klam t, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hb : infer fuel (Δ.map (Kind.kren Nat.succ)) (Γ.map (Ty.kren Nat.succ)) t with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          obtain ⟨ih, hC⟩ := infer_sound fuel t hΓ.klift hb
          rw [kctxOf_klift, ctxOf_klift] at ih
          rw [kctxOf_klift] at hC
          exact ⟨Typed.kgen ih, Kinded.kall hC⟩
  | .kapp t K, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          obtain ⟨tyT, kT⟩ := infer_sound fuel t hΓ ht
          obtain ⟨P, sT, rfl⟩ := kappResult_inv h
          have kAll := kT.steps sT
          cases kAll with
          | kall kP =>
              have t' := Typed.conv tyT kT (Kinded.kall kP) sT.join_left
              exact ⟨Typed.kinst K t', kP.kinst K⟩
  | .orc, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases h
      exact ⟨Typed.orc rfl, Kinded.arr (Kinded.nat _) (Kinded.nat _)⟩

theorem goodCtx_nil (Δ : List Kind) : GoodCtx Δ [] := fun _ _ h => nomatch h

end BusyLean.Fk
