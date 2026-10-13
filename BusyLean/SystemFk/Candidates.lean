import BusyLean.SystemFk.Typing
import BusyLean.SystemFw.Candidates

/-!
# Strong normalization of kind-polymorphic System Fω (with oracle)

Fω's candidate semantics plus a *kind valuation* `θ : ℕ → Fw.Kind` assigning
closed kinds to kind variables. Kind annotations are evaluated under `θ`.
`∀κ. A` is interpreted as the intersection over **all closed kinds** of the
interpretations of `A`. This countable intersection is the whole new
ingredient, and it is why kinds may not quantify over kinds: then the
intersection would range over a domain that includes the very kind being
defined.
-/

namespace BusyLean.Fk

open BusyLean.F (Tm Cand snCand arrCand Step SN)
open BusyLean.Fw (Sem dflt SVal scons allK)
open Ty
open Kind (evalK θcons evalK_kren evalK_ksubst evalK_succ)

variable {f : Nat → Nat}

/-- Intersection over all closed kinds. -/
def kallC (F : Fw.Kind → Cand f) : Cand f where
  P t := ∀ K, (F K).P t
  cr1 h := (F .star).cr1 (h _)
  cr2 h s K := (F K).cr2 (h K) s
  cr3 ht h K := (F K).cr3 ht fun u s => h u s K

/-- Interpretation under a kind valuation `θ` and a type valuation `ρ`, at an
expected closed kind. -/
def interp (θ : Nat → Fw.Kind) (ρ : Nat → SVal f) : Ty → (k : Fw.Kind) → Sem f k
  | tvar n, k => (ρ n).get k
  | arr A B, .star => arrCand (interp θ ρ A .star) (interp θ ρ B .star)
  | arr _ _, .arr k₁ k₂ => dflt f (.arr k₁ k₂)
  | all K A, .star => allK (evalK θ K) fun X => interp θ (scons ⟨evalK θ K, X⟩ ρ) A .star
  | all _ _, .arr k₁ k₂ => dflt f (.arr k₁ k₂)
  | lam _ _, .star => dflt f .star
  | lam _ A, .arr k₁ k₂ => fun X => interp θ (scons ⟨k₁, X⟩ ρ) A k₂
  | app K A B, k => interp θ ρ A (.arr (evalK θ K) k) (interp θ ρ B (evalK θ K))
  | kall A, .star => kallC fun K => interp (θcons K θ) ρ A .star
  | kall _, .arr k₁ k₂ => dflt f (.arr k₁ k₂)

def WK (θ : Nat → Fw.Kind) (Δ : KCtx) (ρ : Nat → SVal f) : Prop :=
  ∀ n, (ρ n).kind = evalK θ (Δ n)

theorem WK.cons {θ : Nat → Fw.Kind} {Δ : KCtx} {ρ : Nat → SVal f} (h : WK θ Δ ρ)
    (k : Kind) (X : Sem f (evalK θ k)) : WK θ (kcons k Δ) (scons ⟨evalK θ k, X⟩ ρ) := fun n => by
  cases n with
  | zero => rfl
  | succ n => exact h n

theorem WK.klift {θ : Nat → Fw.Kind} {Δ : KCtx} {ρ : Nat → SVal f} (h : WK θ Δ ρ)
    (K : Fw.Kind) : WK (θcons K θ) Δ.klift ρ := fun n => by
  rw [h n]
  exact (evalK_succ (Δ n) K θ).symm

/-! ## Renaming and substitution -/

theorem interp_tren : ∀ (A : Ty) (θ : Nat → Fw.Kind) (ρ : Nat → SVal f) (ξ : Nat → Nat)
    (k : Fw.Kind), interp θ ρ (tren ξ A) k = interp θ (ρ ∘ ξ) A k
  | tvar _, _, _, _, _ => rfl
  | arr A B, θ, ρ, ξ, k => by
      cases k with
      | star => show arrCand _ _ = arrCand _ _; rw [interp_tren A, interp_tren B]
      | arr _ _ => rfl
  | all K A, θ, ρ, ξ, k => by
      cases k with
      | star =>
          show allK _ _ = allK _ _
          congr 1; funext X
          rw [interp_tren A]
          congr 1; funext n; cases n <;> rfl
      | arr _ _ => rfl
  | lam K A, θ, ρ, ξ, k => by
      cases k with
      | star => rfl
      | arr k₁ k₂ =>
          funext X
          show interp θ _ (tren _ A) k₂ = interp θ _ A k₂
          rw [interp_tren A]
          congr 1; funext n; cases n <;> rfl
  | app K A B, θ, ρ, ξ, k => by
      show interp θ ρ (tren ξ A) (.arr (evalK θ K) k) (interp θ ρ (tren ξ B) (evalK θ K)) = _
      rw [interp_tren A, interp_tren B]
      rfl
  | kall A, θ, ρ, ξ, k => by
      cases k with
      | star => show kallC _ = kallC _; congr 1; funext K; exact interp_tren A _ ρ ξ _
      | arr _ _ => rfl

theorem interp_kren : ∀ (A : Ty) (θ : Nat → Fw.Kind) (ρ : Nat → SVal f) (ξ : Nat → Nat)
    (k : Fw.Kind), interp θ ρ (Ty.kren ξ A) k = interp (θ ∘ ξ) ρ A k
  | tvar _, _, _, _, _ => rfl
  | arr A B, θ, ρ, ξ, k => by
      cases k with
      | star => show arrCand _ _ = arrCand _ _; rw [interp_kren A, interp_kren B]
      | arr _ _ => rfl
  | all K A, θ, ρ, ξ, k => by
      cases k with
      | star =>
          show allK (evalK θ (K.kren ξ)) _ = allK (evalK (θ ∘ ξ) K) _
          rw [evalK_kren]
          congr 1; funext X
          rw [interp_kren A]
      | arr _ _ => rfl
  | lam K A, θ, ρ, ξ, k => by
      cases k with
      | star => rfl
      | arr k₁ k₂ => funext X; exact interp_kren A θ _ ξ k₂
  | app K A B, θ, ρ, ξ, k => by
      show interp θ ρ (Ty.kren ξ A) (.arr (evalK θ (K.kren ξ)) k)
          (interp θ ρ (Ty.kren ξ B) (evalK θ (K.kren ξ))) = _
      rw [interp_kren A, interp_kren B, evalK_kren]
      rfl
  | kall A, θ, ρ, ξ, k => by
      cases k with
      | star =>
          show kallC _ = kallC _
          congr 1; funext K
          rw [interp_kren A]
          congr 1; funext n; cases n <;> rfl
      | arr _ _ => rfl

theorem interp_ksubst : ∀ (A : Ty) (θ : Nat → Fw.Kind) (ρ : Nat → SVal f) (κs : Nat → Kind)
    (k : Fw.Kind), interp θ ρ (Ty.ksubst κs A) k = interp (fun n => evalK θ (κs n)) ρ A k
  | tvar _, _, _, _, _ => rfl
  | arr A B, θ, ρ, κs, k => by
      cases k with
      | star => show arrCand _ _ = arrCand _ _; rw [interp_ksubst A, interp_ksubst B]
      | arr _ _ => rfl
  | all K A, θ, ρ, κs, k => by
      cases k with
      | star =>
          show allK (evalK θ (K.ksubst κs)) _ = allK (evalK _ K) _
          rw [evalK_ksubst]
          congr 1; funext X
          rw [interp_ksubst A]
      | arr _ _ => rfl
  | lam K A, θ, ρ, κs, k => by
      cases k with
      | star => rfl
      | arr k₁ k₂ => funext X; exact interp_ksubst A θ _ κs k₂
  | app K A B, θ, ρ, κs, k => by
      show interp θ ρ (Ty.ksubst κs A) (.arr (evalK θ (K.ksubst κs)) k)
          (interp θ ρ (Ty.ksubst κs B) (evalK θ (K.ksubst κs))) = _
      rw [interp_ksubst A, interp_ksubst B, evalK_ksubst]
      rfl
  | kall A, θ, ρ, κs, k => by
      cases k with
      | star =>
          show kallC _ = kallC _
          congr 1; funext K
          rw [interp_ksubst A]
          congr 1; funext n
          cases n with
          | zero => rfl
          | succ n => exact evalK_succ (κs n) K θ
      | arr _ _ => rfl

theorem interp_subst {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ (θ : Nat → Fw.Kind) (ρ : Nat → SVal f) (σ : Nat → Ty),
      interp θ ρ (tsubst σ A) (evalK θ k) =
        interp θ (fun n => ⟨evalK θ (Δ n), interp θ ρ (σ n) (evalK θ (Δ n))⟩) A (evalK θ k) := by
  induction h with
  | tvar n =>
      intro θ ρ σ
      show interp θ ρ (σ n) _ = SVal.get ⟨_, interp θ ρ (σ n) _⟩ _
      rw [SVal.get_self]
  | arr _ _ ih₁ ih₂ =>
      intro θ ρ σ
      show arrCand _ _ = arrCand _ _
      have h₁ := ih₁ θ ρ σ
      have h₂ := ih₂ θ ρ σ
      simp only [evalK] at h₁ h₂
      rw [h₁, h₂]
  | @all Δ K A _ ih =>
      intro θ ρ σ
      show allK _ _ = allK _ _
      congr 1; funext X
      have := ih θ (scons ⟨evalK θ K, X⟩ ρ) (tup σ)
      refine this.trans ?_
      congr 1; funext n
      cases n with
      | zero =>
          show SVal.mk (evalK θ K) (SVal.get ⟨evalK θ K, X⟩ (evalK θ K)) = ⟨evalK θ K, X⟩
          rw [SVal.get_self]
      | succ n =>
          show SVal.mk (evalK θ (Δ n))
              (interp θ (scons ⟨evalK θ K, X⟩ ρ) (tren Nat.succ (σ n)) (evalK θ (Δ n))) = _
          rw [interp_tren]
          rfl
  | @lam Δ k₁ k₂ A _ ih =>
      intro θ ρ σ
      funext X
      have := ih θ (scons ⟨evalK θ k₁, X⟩ ρ) (tup σ)
      refine this.trans ?_
      congr 1; funext n
      cases n with
      | zero =>
          show SVal.mk (evalK θ k₁) (SVal.get ⟨evalK θ k₁, X⟩ (evalK θ k₁)) = ⟨evalK θ k₁, X⟩
          rw [SVal.get_self]
      | succ n =>
          show SVal.mk (evalK θ (Δ n))
              (interp θ (scons ⟨evalK θ k₁, X⟩ ρ) (tren Nat.succ (σ n)) (evalK θ (Δ n))) = _
          rw [interp_tren]
          rfl
  | @app Δ k₁ k₂ A B _ _ ih₁ ih₂ =>
      intro θ ρ σ
      show interp θ ρ (tsubst σ A) (.arr (evalK θ k₁) (evalK θ k₂))
          (interp θ ρ (tsubst σ B) (evalK θ k₁)) = _
      have h₁ := ih₁ θ ρ σ
      have h₂ := ih₂ θ ρ σ
      simp only [evalK] at h₁
      rw [h₁, h₂]
      rfl
  | @kall Δ A _ ih =>
      intro θ ρ σ
      show kallC _ = kallC _
      congr 1; funext K
      have := ih (θcons K θ) ρ (tkup σ)
      refine this.trans ?_
      congr 1; funext n
      show SVal.mk (evalK (θcons K θ) ((Δ n).kren Nat.succ))
          (interp (θcons K θ) ρ (Ty.kren Nat.succ (σ n))
            (evalK (θcons K θ) ((Δ n).kren Nat.succ))) =
        SVal.mk (evalK θ (Δ n)) (interp θ ρ (σ n) (evalK θ (Δ n)))
      rw [evalK_succ, interp_kren]
      rfl

theorem interp_inst {θ : Nat → Fw.Kind} {Δ : KCtx} {k k' : Kind} {A : Ty} (B : Ty)
    (hA : Kinded (kcons k Δ) A k') {ρ : Nat → SVal f} (hρ : WK θ Δ ρ) :
    interp θ ρ (Ty.inst A B) (evalK θ k') =
      interp θ (scons ⟨evalK θ k, interp θ ρ B (evalK θ k)⟩ ρ) A (evalK θ k') := by
  unfold Ty.inst
  rw [interp_subst hA]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => exact SVal.eta (hρ n)

theorem interp_kinst (θ : Nat → Fw.Kind) (ρ : Nat → SVal f) (A : Ty) (K : Kind) (k : Fw.Kind) :
    interp θ ρ (Ty.kinst A K) k = interp (θcons (evalK θ K) θ) ρ A k := by
  unfold Ty.kinst
  rw [interp_ksubst]
  congr 1
  funext n
  cases n <;> rfl

/-! ## Conversion -/

theorem interp_step {Δ : KCtx} {A B : Ty} {k : Kind} (h : Kinded Δ A k) (s : TStep A B)
    {θ : Nat → Fw.Kind} {ρ : Nat → SVal f} (hρ : WK θ Δ ρ) :
    interp θ ρ A (evalK θ k) = interp θ ρ B (evalK θ k) := by
  induction s generalizing Δ k θ ρ with
  | beta k₁ k' A B =>
      cases h with
      | app hA hB =>
          cases hA with
          | lam hA' =>
              show interp θ (scons ⟨evalK θ k₁, interp θ ρ B (evalK θ k₁)⟩ ρ) A (evalK θ k) = _
              rw [interp_inst B hA' hρ]
  | arrL _ _ ih =>
      cases h with
      | arr h₁ _ =>
          have e := ih h₁ hρ
          simp only [evalK] at e
          show arrCand _ _ = arrCand _ _
          rw [e]
  | arrR _ _ ih =>
      cases h with
      | arr _ h₂ =>
          have e := ih h₂ hρ
          simp only [evalK] at e
          show arrCand _ _ = arrCand _ _
          rw [e]
  | all K _ ih =>
      cases h with
      | all h₁ =>
          show allK _ _ = allK _ _
          congr 1; funext X
          exact ih h₁ (hρ.cons K X)
  | lam K _ ih =>
      cases h with
      | @lam _ _ k₂ A₀ h₁ =>
          funext X
          exact ih h₁ (hρ.cons K X)
  | @appL k' A A' B _ ih =>
      cases h with
      | app h₁ _ =>
          show interp θ ρ A (.arr (evalK θ k') (evalK θ k)) (interp θ ρ B (evalK θ k')) =
            interp θ ρ A' (.arr (evalK θ k') (evalK θ k)) (interp θ ρ B (evalK θ k'))
          have := ih h₁ hρ
          simp only [evalK] at this
          rw [this]
  | @appR k' A B B' _ ih =>
      cases h with
      | app _ h₂ =>
          show interp θ ρ A (.arr (evalK θ k') (evalK θ k)) (interp θ ρ B (evalK θ k')) =
            interp θ ρ A (.arr (evalK θ k') (evalK θ k)) (interp θ ρ B' (evalK θ k'))
          rw [ih h₂ hρ]
  | kall _ ih =>
      cases h with
      | kall h₁ =>
          show kallC _ = kallC _
          congr 1; funext K
          exact ih h₁ (hρ.klift K)

theorem interp_steps {Δ : KCtx} {A B : Ty} {k : Kind} (h : Kinded Δ A k) (s : TSteps A B)
    {θ : Nat → Fw.Kind} {ρ : Nat → SVal f} (hρ : WK θ Δ ρ) :
    interp θ ρ A (evalK θ k) = interp θ ρ B (evalK θ k) := by
  induction s with
  | refl => rfl
  | step s _ ih => exact (interp_step h s hρ).trans (ih (h.step s))

theorem interp_join {Δ : KCtx} {A B : Ty} {k : Kind} (hA : Kinded Δ A k) (hB : Kinded Δ B k)
    (j : TJoin A B) {θ : Nat → Fw.Kind} {ρ : Nat → SVal f} (hρ : WK θ Δ ρ) :
    interp θ ρ A (evalK θ k) = interp θ ρ B (evalK θ k) := by
  obtain ⟨C, sA, sB⟩ := j
  exact (interp_steps hA sA hρ).trans (interp_steps hB sB hρ).symm

/-! ## Adequacy and strong normalization -/

def OrcOK (f : Nat → Nat) : Prop :=
  ∀ (θ : Nat → Fw.Kind) (ρ : Nat → SVal f), (interp θ ρ (arr Ty.nat Ty.nat) .star).P Tm.orc

theorem adequacy {o : Bool} {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed o Δ Γ t A)
    (ho : o = true → OrcOK f) :
    ∀ (θ : Nat → Fw.Kind) (ρ : Nat → SVal f), WK θ Δ ρ → ∀ (σ : Nat → Tm),
      (∀ n, (interp θ ρ (Γ n) .star).P (σ n)) → (interp θ ρ A .star).P (Tm.subst σ t) := by
  induction ht with
  | var n => intro θ ρ _ σ h; exact h n
  | lam _ ih =>
      intro θ ρ hρ σ h
      refine F.lam_mem fun a ha => ?_
      rw [Tm.subst_beta]
      exact ih θ ρ hρ (Tm.cons a σ) fun n => by
        cases n with
        | zero => exact ha
        | succ n => exact h n
  | app _ _ ih₁ ih₂ => intro θ ρ hρ σ h; exact ih₁ θ ρ hρ σ h _ (ih₂ θ ρ hρ σ h)
  | @gen Δ Γ k A t _ ih =>
      intro θ ρ hρ σ h X
      refine ih θ (scons ⟨evalK θ k, X⟩ ρ) (hρ.cons k X) σ fun n => ?_
      show (interp θ (scons ⟨evalK θ k, X⟩ ρ) (tren Nat.succ (Γ n)) .star).P (σ n)
      rw [interp_tren]
      exact h n
  | @inst Δ Γ k A t B _ hA _ ih =>
      intro θ ρ hρ σ h
      have hall := ih θ ρ hρ σ h (interp θ ρ B (evalK θ k))
      have e := interp_inst (f := f) B hA hρ (k' := .star)
      show (interp θ ρ (Ty.inst A B) (evalK θ .star)).P _
      rw [e]
      exact hall
  | conv _ hA hB j ih =>
      intro θ ρ hρ σ h
      have e := interp_join (f := f) hA hB j hρ
      show (interp θ ρ _ (evalK θ .star)).P _
      rw [← e]
      exact ih θ ρ hρ σ h
  | @kgen Δ Γ A t _ ih =>
      intro θ ρ hρ σ h K
      refine ih (θcons K θ) ρ (hρ.klift K) σ fun n => ?_
      show (interp (θcons K θ) ρ (Ty.kren Nat.succ (Γ n)) .star).P (σ n)
      rw [interp_kren]
      exact h n
  | @kinst Δ Γ A t K _ ih =>
      intro θ ρ hρ σ h
      rw [interp_kinst]
      exact ih θ ρ hρ σ h (evalK θ K)
  | orc e => intro θ ρ _ σ _; exact ho e θ ρ

theorem sn_of_typed' {o : Bool} {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty}
    (ht : Typed o Δ Γ t A) (ho : o = true → OrcOK f) : SN f t := by
  have h := adequacy ht ho (fun _ => .star) (fun n => ⟨evalK (fun _ => .star) (Δ n), dflt f _⟩)
    (fun _ => rfl) Tm.var fun n => (interp _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact (interp _ _ A .star).cr1 h

theorem num_mem (θ : Nat → Fw.Kind) (ρ : Nat → SVal f) (n : Nat) :
    (interp θ ρ Ty.nat .star).P (Tm.num n) := by
  have h := adequacy (f := f)
    (typed_num false (fun _ => Kind.star) (fun _ => Ty.nat) n)
    (fun e => Bool.noConfusion e) θ (fun k => ⟨evalK θ .star, dflt f _⟩) (fun _ => rfl)
    Tm.var fun k => (interp θ _ Ty.nat .star).var k
  rw [Tm.subst_var] at h
  -- The interpretation of the closed type `nat` does not depend on `ρ`.
  have e : interp θ (fun _ => (⟨evalK θ .star, dflt f _⟩ : SVal f)) Ty.nat .star =
      interp θ ρ Ty.nat .star := rfl
  rw [e] at h
  exact h

theorem orcOK (f : Nat → Nat) : OrcOK f := by
  intro θ ρ a ha
  have hsn := (interp θ ρ Ty.nat .star).cr1 ha
  revert ha
  induction hsn with
  | intro a _ ih =>
      intro ha
      refine (interp θ ρ Ty.nat .star).cr3 trivial fun v s => ?_
      cases s with
      | delta n => exact num_mem θ ρ (f n)
      | appL _ s => exact nomatch s
      | appR _ s => exact ih _ s ((interp θ ρ Ty.nat .star).cr2 ha s)

/-- **Strong normalization of kind-polymorphic System Fω with oracle.** -/
theorem sn_of_typed {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed true Δ Γ t A) :
    SN f t :=
  sn_of_typed' ht fun _ => orcOK f

end BusyLean.Fk
