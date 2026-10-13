import BusyLean.SystemFw.Typing
import BusyLean.SystemF.Candidates

/-!
# Strong normalization of System Fω (with oracle)

Girard's candidates, lifted to kinds: the semantic domain of kind `★` is the
type of reducibility candidates, and that of `κ₁ → κ₂` is the type of *Lean
functions* between the domains. Type-level β-reduction is then literally
function application, which is why conversion preserves the interpretation.

Raw type constructors are interpreted at an *expected* kind, with a default
value on kind mismatch (the same dynamic-cast idea as the raw-term
interpreters of Contenders 5 and 6). The substitution and conversion lemmas
are proved for well-kinded types, and the typing rules guarantee kinding
wherever it is needed.
-/

namespace BusyLean.Fw

open BusyLean.F (Tm Cand snCand arrCand Step SN)
open Ty

/-- Semantic domains, by recursion on kinds. -/
def Sem (f : Nat → Nat) : Kind → Type
  | .star => Cand f
  | .arr k₁ k₂ => Sem f k₁ → Sem f k₂

/-- A default inhabitant of every domain. -/
def dflt (f : Nat → Nat) : (k : Kind) → Sem f k
  | .star => snCand f
  | .arr _ k₂ => fun _ => dflt f k₂

/-- A semantic value of some kind. -/
structure SVal (f : Nat → Nat) where
  kind : Kind
  val : Sem f kind

variable {f : Nat → Nat}

/-- Read a semantic value at an expected kind (default on mismatch). -/
def SVal.get (x : SVal f) (k : Kind) : Sem f k :=
  if h : x.kind = k then h ▸ x.val else dflt f k

theorem SVal.get_self (k : Kind) (v : Sem f k) : (SVal.mk k v).get k = v := by
  unfold SVal.get
  rw [dite_eq_left rfl]

theorem SVal.eta {x : SVal f} {k : Kind} (h : x.kind = k) : SVal.mk k (x.get k) = x := by
  obtain ⟨k', v⟩ := x
  cases h
  rw [SVal.get_self]

def scons (x : SVal f) (ρ : Nat → SVal f) : Nat → SVal f
  | 0 => x
  | n + 1 => ρ n

/-- Intersection over all semantic values of kind `k`. -/
def allK (k : Kind) (F : Sem f k → Cand f) : Cand f where
  P t := ∀ X, (F X).P t
  cr1 h := (F (dflt f k)).cr1 (h _)
  cr2 h s X := (F X).cr2 (h X) s
  cr3 ht h X := (F X).cr3 ht fun u s => h u s X

/-- The interpretation of a type constructor at an expected kind. -/
def interp (ρ : Nat → SVal f) : Ty → (k : Kind) → Sem f k
  | tvar n, k => (ρ n).get k
  | arr A B, .star => arrCand (interp ρ A .star) (interp ρ B .star)
  | arr _ _, .arr k₁ k₂ => dflt f (.arr k₁ k₂)
  | all k' A, .star => allK k' fun X => interp (scons ⟨k', X⟩ ρ) A .star
  | all _ _, .arr k₁ k₂ => dflt f (.arr k₁ k₂)
  | lam _ _, .star => dflt f .star
  | lam _ A, .arr k₁ k₂ => fun X => interp (scons ⟨k₁, X⟩ ρ) A k₂
  | app k₁ A B, k => interp ρ A (.arr k₁ k) (interp ρ B k₁)

/-- A valuation respects a kind context. -/
def WK (Δ : KCtx) (ρ : Nat → SVal f) : Prop := ∀ n, (ρ n).kind = Δ n

theorem WK.cons {Δ : KCtx} {ρ : Nat → SVal f} (h : WK Δ ρ) (k : Kind) (X : Sem f k) :
    WK (kcons k Δ) (scons ⟨k, X⟩ ρ) := fun n => by
  cases n with
  | zero => rfl
  | succ n => exact h n

/-! ## Renaming and substitution -/

theorem interp_ren : ∀ (A : Ty) (ρ : Nat → SVal f) (ξ : Nat → Nat) (k : Kind),
    interp ρ (tren ξ A) k = interp (ρ ∘ ξ) A k
  | tvar _, _, _, _ => rfl
  | arr A B, ρ, ξ, k => by
      cases k with
      | star =>
          show arrCand _ _ = arrCand _ _
          rw [interp_ren A, interp_ren B]
      | arr _ _ => rfl
  | all k' A, ρ, ξ, k => by
      cases k with
      | star =>
          show allK _ _ = allK _ _
          congr 1
          funext X
          rw [interp_ren A]
          congr 1
          funext n
          cases n <;> rfl
      | arr _ _ => rfl
  | lam k' A, ρ, ξ, k => by
      cases k with
      | star => rfl
      | arr k₁ k₂ =>
          funext X
          show interp _ (tren _ A) k₂ = interp _ A k₂
          rw [interp_ren A]
          congr 1
          funext n
          cases n <;> rfl
  | app k₁ A B, ρ, ξ, k => by
      show interp ρ (tren ξ A) (.arr k₁ k) (interp ρ (tren ξ B) k₁) = _
      rw [interp_ren A, interp_ren B]
      rfl

theorem interp_subst {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ (ρ : Nat → SVal f) (σ : Nat → Ty),
      interp ρ (tsubst σ A) k = interp (fun n => ⟨Δ n, interp ρ (σ n) (Δ n)⟩) A k := by
  induction h with
  | tvar n =>
      intro ρ σ
      show interp ρ (σ n) _ = SVal.get ⟨_, interp ρ (σ n) _⟩ _
      rw [SVal.get_self]
  | arr _ _ ih₁ ih₂ =>
      intro ρ σ
      show arrCand _ _ = arrCand _ _
      rw [ih₁, ih₂]
  | @all Δ k A _ ih =>
      intro ρ σ
      show allK _ _ = allK _ _
      congr 1
      funext X
      rw [ih]
      congr 1
      funext n
      cases n with
      | zero =>
          show SVal.mk k (SVal.get ⟨k, X⟩ k) = ⟨k, X⟩
          rw [SVal.get_self]
      | succ n =>
          show SVal.mk (Δ n) (interp (scons ⟨k, X⟩ ρ) (tren Nat.succ (σ n)) (Δ n)) = _
          rw [interp_ren]
          rfl
  | @lam Δ k₁ k₂ A _ ih =>
      intro ρ σ
      funext X
      show interp _ (tsubst (tup σ) A) k₂ = _
      rw [ih]
      congr 1
      funext n
      cases n with
      | zero =>
          show SVal.mk k₁ (SVal.get ⟨k₁, X⟩ k₁) = ⟨k₁, X⟩
          rw [SVal.get_self]
      | succ n =>
          show SVal.mk (Δ n) (interp (scons ⟨k₁, X⟩ ρ) (tren Nat.succ (σ n)) (Δ n)) = _
          rw [interp_ren]
          rfl
  | @app Δ k₁ k₂ A B _ _ ih₁ ih₂ =>
      intro ρ σ
      show interp ρ (tsubst σ A) (.arr k₁ k₂) (interp ρ (tsubst σ B) k₁) = _
      rw [ih₁, ih₂]
      rfl

theorem interp_inst {Δ : KCtx} {k k' : Kind} {A : Ty} (B : Ty) (hA : Kinded (kcons k Δ) A k')
    {ρ : Nat → SVal f} (hρ : WK Δ ρ) :
    interp ρ (Ty.inst A B) k' = interp (scons ⟨k, interp ρ B k⟩ ρ) A k' := by
  unfold Ty.inst
  rw [interp_subst hA]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => exact SVal.eta (hρ n)

/-! ## Conversion preserves the interpretation -/

theorem interp_step {Δ : KCtx} {A B : Ty} {k : Kind} (h : Kinded Δ A k) (s : TStep A B)
    {ρ : Nat → SVal f} (hρ : WK Δ ρ) : interp ρ A k = interp ρ B k := by
  induction s generalizing Δ k ρ with
  | beta k₁ k' A B =>
      cases h with
      | app hA hB =>
          cases hA with
          | lam hA' =>
              show interp (scons ⟨k₁, interp ρ B k₁⟩ ρ) A k = _
              rw [interp_inst B hA' hρ]
  | arrL _ _ ih =>
      cases h with
      | arr h₁ _ =>
          show arrCand _ _ = arrCand _ _
          rw [ih h₁ hρ]
  | arrR _ _ ih =>
      cases h with
      | arr _ h₂ =>
          show arrCand _ _ = arrCand _ _
          rw [ih h₂ hρ]
  | all k' _ ih =>
      cases h with
      | all h₁ =>
          show allK _ _ = allK _ _
          congr 1
          funext X
          exact ih h₁ (hρ.cons k' X)
  | lam k' _ ih =>
      cases h with
      | lam h₁ =>
          funext X
          exact ih h₁ (hρ.cons _ X)
  | @appL k' A A' B _ ih =>
      cases h with
      | app h₁ _ =>
          show interp ρ A (.arr k' k) (interp ρ B k') = interp ρ A' (.arr k' k) (interp ρ B k')
          rw [ih h₁ hρ]
  | @appR k' A B B' _ ih =>
      cases h with
      | app _ h₂ =>
          show interp ρ A (.arr k' k) (interp ρ B k') = interp ρ A (.arr k' k) (interp ρ B' k')
          rw [ih h₂ hρ]

theorem interp_steps {Δ : KCtx} {A B : Ty} {k : Kind} (h : Kinded Δ A k) (s : TSteps A B)
    {ρ : Nat → SVal f} (hρ : WK Δ ρ) : interp ρ A k = interp ρ B k := by
  induction s with
  | refl => rfl
  | step s _ ih => exact (interp_step h s hρ).trans (ih (h.step s))

theorem interp_join {Δ : KCtx} {A B : Ty} {k : Kind} (hA : Kinded Δ A k) (hB : Kinded Δ B k)
    (j : TJoin A B) {ρ : Nat → SVal f} (hρ : WK Δ ρ) : interp ρ A k = interp ρ B k := by
  obtain ⟨C, sA, sB⟩ := j
  exact (interp_steps hA sA hρ).trans (interp_steps hB sB hρ).symm

/-! ## Adequacy and strong normalization -/

def OrcOK (f : Nat → Nat) : Prop :=
  ∀ ρ : Nat → SVal f, (interp ρ (arr Ty.nat Ty.nat) .star).P Tm.orc

theorem adequacy {o : Bool} {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed o Δ Γ t A)
    (ho : o = true → OrcOK f) :
    ∀ (ρ : Nat → SVal f), WK Δ ρ → ∀ (σ : Nat → Tm),
      (∀ n, (interp ρ (Γ n) .star).P (σ n)) → (interp ρ A .star).P (Tm.subst σ t) := by
  induction ht with
  | var n => intro ρ _ σ h; exact h n
  | lam _ ih =>
      intro ρ hρ σ h
      refine F.lam_mem fun a ha => ?_
      rw [Tm.subst_beta]
      exact ih ρ hρ (Tm.cons a σ) fun n => by
        cases n with
        | zero => exact ha
        | succ n => exact h n
  | app _ _ ih₁ ih₂ => intro ρ hρ σ h; exact ih₁ ρ hρ σ h _ (ih₂ ρ hρ σ h)
  | @gen Δ Γ k A t _ ih =>
      intro ρ hρ σ h X
      refine ih (scons ⟨k, X⟩ ρ) (hρ.cons k X) σ fun n => ?_
      show (interp (scons ⟨k, X⟩ ρ) (tren Nat.succ (Γ n)) .star).P (σ n)
      rw [interp_ren]
      exact h n
  | @inst Δ Γ k A t B _ hA _ ih =>
      intro ρ hρ σ h
      have hall := ih ρ hρ σ h (interp ρ B k)
      rw [interp_inst B hA hρ]
      exact hall
  | conv _ hA hB j ih =>
      intro ρ hρ σ h
      rw [← interp_join hA hB j hρ]
      exact ih ρ hρ σ h
  | orc e => intro ρ _ σ _; exact ho e ρ

/-- The default valuation for a kind context. -/
def ρ₀ (f : Nat → Nat) (Δ : KCtx) : Nat → SVal f := fun n => ⟨Δ n, dflt f (Δ n)⟩

theorem sn_of_typed' {o : Bool} {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty}
    (ht : Typed o Δ Γ t A) (ho : o = true → OrcOK f) : SN f t := by
  have h := adequacy ht ho (ρ₀ f Δ) (fun _ => rfl) Tm.var fun n => (interp _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact (interp _ A .star).cr1 h

theorem num_mem (ρ : Nat → SVal f) (n : Nat) : (interp ρ Ty.nat .star).P (Tm.num n) := by
  have h := adequacy (f := f) (typed_num false (fun k => (ρ k).kind) (fun _ => Ty.nat) n)
    (fun e => Bool.noConfusion e) ρ (fun _ => rfl) Tm.var fun k => (interp ρ Ty.nat .star).var k
  rwa [Tm.subst_var] at h

theorem orcOK (f : Nat → Nat) : OrcOK f := by
  intro ρ a ha
  have hsn := (interp ρ Ty.nat .star).cr1 ha
  revert ha
  induction hsn with
  | intro a _ ih =>
      intro ha
      refine (interp ρ Ty.nat .star).cr3 trivial fun v s => ?_
      cases s with
      | delta n => exact num_mem ρ (f n)
      | appL _ s => exact nomatch s
      | appR _ s => exact ih _ s ((interp ρ Ty.nat .star).cr2 ha s)

/-- **Strong normalization of System Fω with oracle.** -/
theorem sn_of_typed {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed true Δ Γ t A) :
    SN f t :=
  sn_of_typed' ht fun _ => orcOK f

end BusyLean.Fw
