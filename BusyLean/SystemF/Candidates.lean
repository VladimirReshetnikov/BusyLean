import BusyLean.SystemF.Reduction
import BusyLean.SystemF.Types

/-!
# Strong normalization of System F (with oracle), by reducibility candidates

Girard's method interprets each type as a *reducibility candidate*: a predicate
on terms that implies SN (CR1), is closed under reduction (CR2), and contains
every neutral term all of whose reducts it contains (CR3). The interpretation
of `∀X. A` is the intersection over **all** candidates. This quantification is
impredicative, and Lean allows it because the result lives in `Prop`.

Adequacy (well-typed terms belong to the interpretation of their type) then
gives strong normalization. The oracle `orc : nat → nat` is handled separately,
because its δ-rule fires at the head of an application, so `orc` is not
neutral. Numerals are typed without the oracle rule, hence belong to every
interpretation of `nat`, and the δ-reduct of `orc n̄` is a numeral.
-/

namespace BusyLean.F

open Tm Ty

/-- Terms that cannot create a head redex when applied: not λ, not the oracle. -/
def Neutral : Tm → Prop
  | Tm.lam _ => False
  | Tm.orc => False
  | _ => True

structure Cand (f : Nat → Nat) where
  P : Tm → Prop
  cr1 : ∀ {t}, P t → SN f t
  cr2 : ∀ {t u}, P t → Step f t u → P u
  cr3 : ∀ {t}, Neutral t → (∀ u, Step f t u → P u) → P t

variable {f : Nat → Nat}

theorem Cand.var (C : Cand f) (n : Nat) : C.P (Tm.var n) :=
  C.cr3 trivial fun _ s => nomatch s

/-- SN itself is a candidate. -/
def snCand (f : Nat → Nat) : Cand f where
  P := SN f
  cr1 h := h
  cr2 h s := h.step s
  cr3 _ h := SN.intro h

/-- Steps out of `t a` when `t` is neutral stay inside `t` or `a`. -/
theorem Step.app_neutral_inv {t a v : Tm} (ht : Neutral t) (s : Step f (app t a) v) :
    (∃ t', v = app t' a ∧ Step f t t') ∨ (∃ a', v = app t a' ∧ Step f a a') := by
  cases s with
  | beta b a => exact ht.elim
  | delta n => exact ht.elim
  | appL _ s => exact Or.inl ⟨_, rfl, s⟩
  | appR _ s => exact Or.inr ⟨_, rfl, s⟩

/-- The arrow construction `A → B`. -/
def arrCand (A B : Cand f) : Cand f where
  P t := ∀ a, A.P a → B.P (app t a)
  cr1 h := (B.cr1 (h _ (A.var 0))).of_app_left
  cr2 h s a ha := B.cr2 (h a ha) (Step.appL a s)
  cr3 {t} ht h a ha := by
    have hsn := A.cr1 ha
    revert ha
    induction hsn with
    | intro a _ ih =>
        intro ha
        refine B.cr3 trivial fun v s => ?_
        rcases Step.app_neutral_inv ht s with ⟨t', rfl, s'⟩ | ⟨a', rfl, s'⟩
        · exact h t' s' a ha
        · exact ih a' s' (A.cr2 ha s')

/-- The intersection `∀X. F X` over all candidates. -/
def allCand (F : Cand f → Cand f) : Cand f where
  P t := ∀ C, (F C).P t
  cr1 h := (F (snCand f)).cr1 (h _)
  cr2 h s C := (F C).cr2 (h C) s
  cr3 ht h C := (F C).cr3 ht fun u s => h u s C

def Cand.cons (C : Cand f) (ρ : Nat → Cand f) : Nat → Cand f
  | 0 => C
  | n + 1 => ρ n

/-- The interpretation of types, relative to a candidate valuation `ρ`. -/
def interp (ρ : Nat → Cand f) : Ty → Cand f
  | tvar n => ρ n
  | arr A B => arrCand (interp ρ A) (interp ρ B)
  | all A => allCand fun C => interp (Cand.cons C ρ) A

/-! ## Substitution lemmas for the interpretation -/

theorem interp_ren : ∀ (A : Ty) (ρ : Nat → Cand f) (ξ : Nat → Nat),
    interp ρ (tren ξ A) = interp (ρ ∘ ξ) A
  | tvar _, _, _ => rfl
  | arr A B, ρ, ξ => by
      show arrCand _ _ = arrCand _ _
      rw [interp_ren A, interp_ren B]
  | all A, ρ, ξ => by
      show allCand _ = allCand _
      congr 1
      funext C
      rw [interp_ren A]
      congr 1
      funext n
      cases n <;> rfl

theorem interp_subst : ∀ (A : Ty) (ρ : Nat → Cand f) (σ : Nat → Ty),
    interp ρ (tsubst σ A) = interp (fun n => interp ρ (σ n)) A
  | tvar _, _, _ => rfl
  | arr A B, ρ, σ => by
      show arrCand _ _ = arrCand _ _
      rw [interp_subst A, interp_subst B]
  | all A, ρ, σ => by
      show allCand _ = allCand _
      congr 1
      funext C
      rw [interp_subst A]
      congr 1
      funext n
      cases n with
      | zero => rfl
      | succ n =>
          show interp (Cand.cons C ρ) (tren Nat.succ (σ n)) = interp ρ (σ n)
          rw [interp_ren]
          rfl

/-! ## Adequacy -/

/-- SN is reflected by substitution: reductions of `t` lift to `subst σ t`. -/
theorem SN.of_subst {σ : Nat → Tm} {t : Tm} (h : SN f (subst σ t)) : SN f t := by
  generalize he : subst σ t = s at h
  induction h generalizing t with
  | intro s _ ih =>
      subst he
      exact SN.intro fun t' st => ih _ (st.subst σ) rfl

/-- A λ belongs to `A → B` if all its β-instances by members of `A` lie in `B`. -/
theorem lam_mem {A B : Cand f} {b : Tm}
    (h : ∀ a, A.P a → B.P (subst (cons a Tm.var) b)) : (arrCand A B).P (Tm.lam b) := by
  have hb : SN f b := (B.cr1 (h (Tm.var 0) (A.var 0))).of_subst
  suffices key : ∀ b, SN f b → ∀ a, SN f a →
      (∀ a, A.P a → B.P (subst (cons a Tm.var) b)) → A.P a → B.P (app (Tm.lam b) a) from
    fun a ha => key b hb a (A.cr1 ha) h ha
  intro b hb
  induction hb with
  | intro b _ ihb =>
      intro a ha
      induction ha with
      | intro a hacc iha =>
          intro h ha'
          refine B.cr3 trivial fun v s => ?_
          cases s with
          | beta => exact h a ha'
          | appL _ s =>
              obtain ⟨b', rfl, s'⟩ := s.lam_inv
              exact ihb b' s' a (Acc.intro a hacc)
                (fun a' ha'' => B.cr2 (h a' ha'') (s'.subst _)) ha'
          | appR _ s => exact iha _ s h (A.cr2 ha' s)

/-- The oracle belongs to `nat → nat` in every valuation. -/
def OrcOK (f : Nat → Nat) : Prop := ∀ ρ : Nat → Cand f, (interp ρ (arr Ty.nat Ty.nat)).P Tm.orc

theorem adequacy {o : Bool} {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed o Γ t A)
    (ho : o = true → OrcOK f) :
    ∀ (ρ : Nat → Cand f) (σ : Nat → Tm),
      (∀ n, (interp ρ (Γ n)).P (σ n)) → (interp ρ A).P (subst σ t) := by
  induction ht with
  | var n => intro ρ σ h; exact h n
  | lam _ ih =>
      intro ρ σ h
      refine lam_mem fun a ha => ?_
      rw [subst_beta]
      exact ih ρ (cons a σ) fun n => by
        cases n with
        | zero => exact ha
        | succ n => exact h n
  | app _ _ ih₁ ih₂ => intro ρ σ h; exact ih₁ ρ σ h _ (ih₂ ρ σ h)
  | gen _ ih =>
      intro ρ σ h C
      refine ih (Cand.cons C ρ) σ fun n => ?_
      show (interp (Cand.cons C ρ) (tren Nat.succ _)).P (σ n)
      rw [interp_ren]
      exact h n
  | @inst Γ A t B _ ih =>
      intro ρ σ h
      have hall := ih ρ σ h (interp ρ B)
      show (interp ρ (tsubst (tcons B tvar) A)).P _
      rw [interp_subst]
      have e : (fun n => interp ρ (tcons B tvar n)) = Cand.cons (interp ρ B) ρ := by
        funext n; cases n <;> rfl
      rw [e]
      exact hall
  | orc h => intro ρ σ _; exact ho h ρ

/-- Typable terms are strongly normalizing, given the oracle condition. -/
theorem sn_of_typed' {o : Bool} {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed o Γ t A)
    (ho : o = true → OrcOK f) : SN f t := by
  have h := adequacy ht ho (fun _ => snCand f) Tm.var fun n => (interp _ (Γ n)).var n
  rw [subst_var] at h
  exact (interp _ A).cr1 h

/-- Numerals belong to every interpretation of `nat`. -/
theorem num_mem (ρ : Nat → Cand f) (n : Nat) : (interp ρ Ty.nat).P (num n) := by
  have h := adequacy (f := f) (typed_num false (fun _ => Ty.nat) n)
    (fun h => Bool.noConfusion h) ρ Tm.var fun k => (interp ρ Ty.nat).var k
  rwa [subst_var] at h

/-- The oracle condition holds: `orc a` reduces only inside `a` or to a numeral. -/
theorem orcOK (f : Nat → Nat) : OrcOK f := by
  intro ρ a ha
  have hsn := (interp ρ Ty.nat).cr1 ha
  revert ha
  induction hsn with
  | intro a _ ih =>
      intro ha
      refine (interp ρ Ty.nat).cr3 trivial fun v s => ?_
      cases s with
      | delta n => exact num_mem ρ (f n)
      | appL _ s => exact nomatch s
      | appR _ s => exact ih _ s ((interp ρ Ty.nat).cr2 ha s)

/-- **Strong normalization**: every term typable in System F with the oracle
is strongly normalizing, for every oracle function `f`. -/
theorem sn_of_typed {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed true Γ t A) : SN f t :=
  sn_of_typed' ht fun _ => orcOK f

end BusyLean.F
