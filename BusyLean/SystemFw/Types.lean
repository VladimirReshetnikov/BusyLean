import BusyLean.SystemF.Syntax

/-!
# System Fω: kinds, type constructors, kinding, type-level β

Type constructors form a simply typed λ-calculus over the base kind `★`, with
`→` and `∀κ` as constants of the base kind. Applications carry the kind of
their argument (`app κ A B` with `B : κ`). That lets the semantics recurse on
syntax alone.

Type equality is β-conversion. The type checker decides it soundly by
fuel-bounded normalization and syntactic comparison. Soundness rests on
`tnf_steps`: what the normalizer returns is a reduct.
-/

namespace BusyLean.Fw

inductive Kind where
  | star : Kind
  | arr : Kind → Kind → Kind
  deriving DecidableEq

inductive Ty where
  | tvar : Nat → Ty
  | arr : Ty → Ty → Ty
  | all : Kind → Ty → Ty
  | lam : Kind → Ty → Ty
  | app : Kind → Ty → Ty → Ty
  deriving DecidableEq

namespace Ty

open BusyLean.F.Tm (upRen)

def tren (ξ : Nat → Nat) : Ty → Ty
  | tvar n => tvar (ξ n)
  | arr A B => arr (tren ξ A) (tren ξ B)
  | all k A => all k (tren (upRen ξ) A)
  | lam k A => lam k (tren (upRen ξ) A)
  | app k A B => app k (tren ξ A) (tren ξ B)

def tcons (B : Ty) (σ : Nat → Ty) : Nat → Ty
  | 0 => B
  | n + 1 => σ n

def tup (σ : Nat → Ty) : Nat → Ty := tcons (tvar 0) (fun n => tren Nat.succ (σ n))

def tsubst (σ : Nat → Ty) : Ty → Ty
  | tvar n => σ n
  | arr A B => arr (tsubst σ A) (tsubst σ B)
  | all k A => all k (tsubst (tup σ) A)
  | lam k A => lam k (tsubst (tup σ) A)
  | app k A B => app k (tsubst σ A) (tsubst σ B)

/-- `A[B/0]`. -/
def inst (A B : Ty) : Ty := tsubst (tcons B tvar) A

/-- Church numerals: `∀X:★. (X → X) → X → X`. -/
def nat : Ty := all .star (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0)))

end Ty

open Ty

/-! ## Kinding -/

abbrev KCtx := Nat → Kind

def kcons (k : Kind) (Δ : KCtx) : KCtx
  | 0 => k
  | n + 1 => Δ n

inductive Kinded : KCtx → Ty → Kind → Prop where
  | tvar {Δ : KCtx} (n : Nat) : Kinded Δ (tvar n) (Δ n)
  | arr {Δ : KCtx} {A B : Ty} :
      Kinded Δ A .star → Kinded Δ B .star → Kinded Δ (arr A B) .star
  | all {Δ : KCtx} {k : Kind} {A : Ty} :
      Kinded (kcons k Δ) A .star → Kinded Δ (all k A) .star
  | lam {Δ : KCtx} {k₁ k₂ : Kind} {A : Ty} :
      Kinded (kcons k₁ Δ) A k₂ → Kinded Δ (lam k₁ A) (.arr k₁ k₂)
  | app {Δ : KCtx} {k₁ k₂ : Kind} {A B : Ty} :
      Kinded Δ A (.arr k₁ k₂) → Kinded Δ B k₁ → Kinded Δ (app k₁ A B) k₂

theorem Kinded.ren {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ {Δ' : KCtx} {ξ : Nat → Nat}, (∀ n, Δ' (ξ n) = Δ n) → Kinded Δ' (tren ξ A) k := by
  induction h with
  | tvar n => intro Δ' ξ hξ; rw [← hξ n]; exact Kinded.tvar _
  | arr _ _ ih₁ ih₂ => intro Δ' ξ hξ; exact Kinded.arr (ih₁ hξ) (ih₂ hξ)
  | all _ ih =>
      intro Δ' ξ hξ
      exact Kinded.all (ih fun n => by cases n <;> simp [kcons, F.Tm.upRen, hξ])
  | lam _ ih =>
      intro Δ' ξ hξ
      exact Kinded.lam (ih fun n => by cases n <;> simp [kcons, F.Tm.upRen, hξ])
  | app _ _ ih₁ ih₂ => intro Δ' ξ hξ; exact Kinded.app (ih₁ hξ) (ih₂ hξ)

theorem Kinded.subst {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ {Δ' : KCtx} {σ : Nat → Ty}, (∀ n, Kinded Δ' (σ n) (Δ n)) →
      Kinded Δ' (tsubst σ A) k := by
  induction h with
  | tvar n => intro Δ' σ hσ; exact hσ n
  | arr _ _ ih₁ ih₂ => intro Δ' σ hσ; exact Kinded.arr (ih₁ hσ) (ih₂ hσ)
  | @all Δ k A _ ih =>
      intro Δ' σ hσ
      refine Kinded.all (ih fun n => ?_)
      cases n with
      | zero => exact Kinded.tvar 0
      | succ n => exact (hσ n).ren fun _ => rfl
  | @lam Δ k₁ k₂ A _ ih =>
      intro Δ' σ hσ
      refine Kinded.lam (ih fun n => ?_)
      cases n with
      | zero => exact Kinded.tvar 0
      | succ n => exact (hσ n).ren fun _ => rfl
  | app _ _ ih₁ ih₂ => intro Δ' σ hσ; exact Kinded.app (ih₁ hσ) (ih₂ hσ)

theorem Kinded.inst {Δ : KCtx} {k k' : Kind} {A B : Ty}
    (hA : Kinded (kcons k Δ) A k') (hB : Kinded Δ B k) : Kinded Δ (Ty.inst A B) k' :=
  hA.subst fun n => by
    cases n with
    | zero => exact hB
    | succ n => exact Kinded.tvar n

theorem Kinded.nat (Δ : KCtx) : Kinded Δ Ty.nat .star :=
  Kinded.all (Kinded.arr (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0))
    (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0)))

/-! ## Type-level β-reduction -/

inductive TStep : Ty → Ty → Prop where
  | beta (k k' : Kind) (A B : Ty) : TStep (app k (lam k' A) B) (Ty.inst A B)
  | arrL {A A' : Ty} (B : Ty) : TStep A A' → TStep (arr A B) (arr A' B)
  | arrR (A : Ty) {B B' : Ty} : TStep B B' → TStep (arr A B) (arr A B')
  | all (k : Kind) {A A' : Ty} : TStep A A' → TStep (all k A) (all k A')
  | lam (k : Kind) {A A' : Ty} : TStep A A' → TStep (lam k A) (lam k A')
  | appL (k : Kind) {A A' : Ty} (B : Ty) : TStep A A' → TStep (app k A B) (app k A' B)
  | appR (k : Kind) (A : Ty) {B B' : Ty} : TStep B B' → TStep (app k A B) (app k A B')

inductive TSteps : Ty → Ty → Prop where
  | refl (A : Ty) : TSteps A A
  | step {A B C : Ty} : TStep A B → TSteps B C → TSteps A C

theorem TSteps.trans {A B C : Ty} (h₁ : TSteps A B) (h₂ : TSteps B C) : TSteps A C := by
  induction h₁ with
  | refl => exact h₂
  | step s _ ih => exact TSteps.step s (ih h₂)

/-- Two types are convertible if they have a common reduct. -/
def TJoin (A B : Ty) : Prop := ∃ C, TSteps A C ∧ TSteps B C

/-- Kinding is preserved by type reduction (subject reduction). -/
theorem Kinded.step {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) {B : Ty}
    (s : TStep A B) : Kinded Δ B k := by
  induction s generalizing Δ k with
  | beta k₁ k' A B =>
      cases h with
      | app hA hB =>
          cases hA with
          | lam hA' => exact hA'.inst hB
  | arrL _ _ ih => cases h with | arr h₁ h₂ => exact Kinded.arr (ih h₁) h₂
  | arrR _ _ ih => cases h with | arr h₁ h₂ => exact Kinded.arr h₁ (ih h₂)
  | all _ _ ih => cases h with | all h₁ => exact Kinded.all (ih h₁)
  | lam _ _ ih => cases h with | lam h₁ => exact Kinded.lam (ih h₁)
  | appL _ _ _ ih => cases h with | app h₁ h₂ => exact Kinded.app (ih h₁) h₂
  | appR _ _ _ ih => cases h with | app h₁ h₂ => exact Kinded.app h₁ (ih h₂)

theorem Kinded.steps {Δ : KCtx} {A B : Ty} {k : Kind} (h : Kinded Δ A k) (s : TSteps A B) :
    Kinded Δ B k := by
  induction s with
  | refl => exact h
  | step s _ ih => exact ih (h.step s)

/-! ## A sound, fuel-bounded type normalizer -/

/-- Normal-order step at a type application, given the steps of its parts. -/
def tappStep (k : Kind) (A B : Ty) (sA sB : Option Ty) : Option Ty :=
  match A with
  | lam _ A₀ => some (Ty.inst A₀ B)
  | _ =>
      match sA with
      | some A' => some (app k A' B)
      | none => sB.map (app k A)

/-- One normal-order type reduction step. -/
def tstep : Ty → Option Ty
  | tvar _ => none
  | arr A B =>
      match tstep A with
      | some A' => some (arr A' B)
      | none => (tstep B).map (arr A)
  | all k A => (tstep A).map (all k)
  | lam k A => (tstep A).map (lam k)
  | app k A B => tappStep k A B (tstep A) (tstep B)

/-- The congruence part of `tappStep`, as a standalone function. -/
def tappCong (k : Kind) (A B : Ty) (sA sB : Option Ty) : Option Ty :=
  match sA with
  | some A' => some (app k A' B)
  | none => sB.map (app k A)

theorem tappCong_sound {k : Kind} {A B C : Ty} {sA sB : Option Ty}
    (hA : ∀ A', sA = some A' → TStep A A') (hB : ∀ B', sB = some B' → TStep B B')
    (h : tappCong k A B sA sB = some C) : TStep (app k A B) C := by
  unfold tappCong at h
  cases sA with
  | some A' => cases h; exact TStep.appL _ _ (hA A' rfl)
  | none =>
      cases sB with
      | none => cases h
      | some B' => cases h; exact TStep.appR _ _ (hB B' rfl)

theorem tappStep_sound {k : Kind} {A B C : Ty} {sA sB : Option Ty}
    (hA : ∀ A', sA = some A' → TStep A A') (hB : ∀ B', sB = some B' → TStep B B')
    (h : tappStep k A B sA sB = some C) : TStep (app k A B) C := by
  cases A with
  | lam k' A₀ => cases h; exact TStep.beta _ _ _ _
  | tvar _ => exact tappCong_sound hA hB h
  | arr _ _ => exact tappCong_sound hA hB h
  | all _ _ => exact tappCong_sound hA hB h
  | app _ _ _ => exact tappCong_sound hA hB h

theorem tstep_sound : ∀ {A B : Ty}, tstep A = some B → TStep A B
  | tvar _, _, h => nomatch h
  | arr A B, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | some A' => rw [hA] at h; cases h; exact TStep.arrL _ (tstep_sound hA)
      | none =>
          rw [hA] at h
          cases hB : tstep B with
          | none => rw [hB] at h; cases h
          | some B' => rw [hB] at h; cases h; exact TStep.arrR _ (tstep_sound hB)
  | all k A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.all _ (tstep_sound hA)
  | lam k A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.lam _ (tstep_sound hA)
  | app k A B, C, h =>
      tappStep_sound (fun _ e => tstep_sound e) (fun _ e => tstep_sound e) h

/-- At most `fuel` normal-order steps. -/
def tnf : Nat → Ty → Ty
  | 0, A => A
  | fuel + 1, A =>
      match tstep A with
      | some B => tnf fuel B
      | none => A

theorem tnf_steps : ∀ (fuel : Nat) (A : Ty), TSteps A (tnf fuel A)
  | 0, A => TSteps.refl A
  | fuel + 1, A => by
      simp only [tnf]
      cases h : tstep A with
      | none => exact TSteps.refl A
      | some B => exact TSteps.step (tstep_sound h) (tnf_steps fuel B)

/-- Sound convertibility test: equal fuel-bounded normal forms. -/
theorem tjoin_of_tnf {fuel : Nat} {A B : Ty} (h : tnf fuel A = tnf fuel B) : TJoin A B :=
  ⟨tnf fuel A, tnf_steps fuel A, h ▸ tnf_steps fuel B⟩

/-! ## Kind inference -/

def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth? xs n

def kctxOf (Δ : List Kind) : KCtx := fun n => (nth? Δ n).getD .star

theorem kctxOf_cons (k : Kind) (Δ : List Kind) : kctxOf (k :: Δ) = kcons k (kctxOf Δ) := by
  funext n; cases n <;> rfl

def inferKind : List Kind → Ty → Option Kind
  | Δ, tvar n => nth? Δ n
  | Δ, arr A B =>
      match inferKind Δ A, inferKind Δ B with
      | some .star, some .star => some .star
      | _, _ => none
  | Δ, all k A =>
      match inferKind (k :: Δ) A with
      | some .star => some .star
      | _ => none
  | Δ, lam k A => (inferKind (k :: Δ) A).map (Kind.arr k)
  | Δ, app k A B =>
      match inferKind Δ A, inferKind Δ B with
      | some (.arr k₁ k₂), some k' => if k₁ = k ∧ k' = k then some k₂ else none
      | _, _ => none

theorem inferKind_sound : ∀ (A : Ty) {Δ : List Kind} {k : Kind},
    inferKind Δ A = some k → Kinded (kctxOf Δ) A k
  | tvar n, Δ, k, h => by
      have e : kctxOf Δ n = k := by
        show (nth? Δ n).getD .star = k
        rw [show nth? Δ n = some k from h]; rfl
      rw [← e]; exact Kinded.tvar n
  | arr A B, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind Δ A with
      | none => rw [hA] at h; cases h
      | some kA =>
          cases hB : inferKind Δ B with
          | none => rw [hA, hB] at h; cases kA <;> cases h
          | some kB =>
              rw [hA, hB] at h
              cases kA with
              | arr _ _ => cases h
              | star =>
                  cases kB with
                  | arr _ _ => cases h
                  | star =>
                      cases h
                      exact Kinded.arr (inferKind_sound A hA) (inferKind_sound B hB)
  | all k' A, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind (k' :: Δ) A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          cases kA with
          | arr _ _ => cases h
          | star =>
              cases h
              have ih := inferKind_sound A hA
              rw [kctxOf_cons] at ih
              exact Kinded.all ih
  | lam k' A, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind (k' :: Δ) A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          cases h
          have ih := inferKind_sound A hA
          rw [kctxOf_cons] at ih
          exact Kinded.lam ih
  | app k' A B, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind Δ A with
      | none => rw [hA] at h; cases h
      | some kA =>
          cases hB : inferKind Δ B with
          | none => rw [hA, hB] at h; cases kA <;> cases h
          | some kB =>
              rw [hA, hB] at h
              cases kA with
              | star => cases h
              | arr k₁ k₂ =>
                  change (if k₁ = k' ∧ kB = k' then some k₂ else none) = some k at h
                  by_cases e : k₁ = k' ∧ kB = k'
                  · rw [ite_eq_left e] at h
                    cases h
                    obtain ⟨rfl, rfl⟩ := e
                    exact Kinded.app (inferKind_sound A hA) (inferKind_sound B hB)
                  · rw [ite_eq_right e] at h; cases h

end BusyLean.Fw
