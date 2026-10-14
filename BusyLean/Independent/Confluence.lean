import BusyLean.SystemF.Normalize

/-!
# Confluence of β (and the oracle rule) on untyped terms

The normalizer `F.nf` follows one particular (normal-order) strategy. To learn
what it returns for a program, it is enough to show *some* reduction sequence
from the program to a Church numeral: by the Church–Rosser theorem below,
normal forms are unique, so `nf` must return that numeral (`nf_eq_of_steps`).

The proof is Takahashi's: parallel reduction `Par`, its complete development
`cd`, and the triangle property `Par t u → Par u (cd t)`. The oracle rule
`orc n̄ ⟶ f(n)‾` fires only on a literal Church numeral, which is already
normal, so it does not overlap with β.
-/

namespace BusyLean.F

open Tm

variable {f : Nat → Nat}

/-! ## Multi-step reduction -/

/-- Reflexive-transitive closure of `Step f`. -/
inductive Steps (f : Nat → Nat) : Tm → Tm → Prop where
  | refl (t : Tm) : Steps f t t
  | head {t u v : Tm} : Step f t u → Steps f u v → Steps f t v

namespace Steps

theorem single {t u : Tm} (s : Step f t u) : Steps f t u := head s (refl u)

theorem trans {t u v : Tm} (h₁ : Steps f t u) (h₂ : Steps f u v) : Steps f t v := by
  induction h₁ with
  | refl => exact h₂
  | head s _ ih => exact head s (ih h₂)

theorem appL {t t' : Tm} (u : Tm) (h : Steps f t t') : Steps f (app t u) (app t' u) := by
  induction h with
  | refl => exact refl _
  | head s _ ih => exact head (Step.appL u s) ih

theorem appR (t : Tm) {u u' : Tm} (h : Steps f u u') : Steps f (app t u) (app t u') := by
  induction h with
  | refl => exact refl _
  | head s _ ih => exact head (Step.appR t s) ih

theorem app {t t' u u' : Tm} (h₁ : Steps f t t') (h₂ : Steps f u u') :
    Steps f (Tm.app t u) (Tm.app t' u') :=
  (appL u h₁).trans (appR t' h₂)

theorem lam {t t' : Tm} (h : Steps f t t') : Steps f (Tm.lam t) (Tm.lam t') := by
  induction h with
  | refl => exact refl _
  | head s _ ih => exact head (Step.lam s) ih

theorem subst {t u : Tm} (h : Steps f t u) (σ : Nat → Tm) :
    Steps f (Tm.subst σ t) (Tm.subst σ u) := by
  induction h with
  | refl => exact refl _
  | head s _ ih => exact head (s.subst σ) ih

theorem ren {t u : Tm} (h : Steps f t u) (ξ : Nat → Nat) : Steps f (Tm.ren ξ t) (Tm.ren ξ u) := by
  rw [ren_eq_subst, ren_eq_subst]
  exact h.subst _

theorem beta (b a : Tm) : Steps f (Tm.app (Tm.lam b) a) (Tm.subst (cons a var) b) :=
  single (Step.beta b a)

end Steps

/-! ## Parallel reduction -/

inductive Par (f : Nat → Nat) : Tm → Tm → Prop where
  | var (n : Nat) : Par f (var n) (var n)
  | orc : Par f orc orc
  | lam {t t' : Tm} : Par f t t' → Par f (lam t) (lam t')
  | app {t t' u u' : Tm} : Par f t t' → Par f u u' → Par f (app t u) (app t' u')
  | beta {b b' a a' : Tm} : Par f b b' → Par f a a' →
      Par f (app (lam b) a) (subst (cons a' var) b')
  | delta (n : Nat) : Par f (app orc (num n)) (num (f n))

theorem Par.refl : ∀ t : Tm, Par f t t
  | .var n => .var n
  | .orc => .orc
  | .lam t => .lam (Par.refl t)
  | .app t u => .app (Par.refl t) (Par.refl u)

theorem Par.of_step {t u : Tm} (s : Step f t u) : Par f t u := by
  induction s with
  | beta b a => exact .beta (Par.refl b) (Par.refl a)
  | delta n => exact .delta n
  | appL u _ ih => exact .app ih (Par.refl u)
  | appR t _ ih => exact .app (Par.refl t) ih
  | lam _ ih => exact .lam ih

theorem ren_beta (b a : Tm) (ξ : Nat → Nat) :
    ren ξ (subst (cons a var) b) = subst (cons (ren ξ a) var) (ren (upRen ξ) b) := by
  rw [ren_eq_subst, subst_cons_comm, up_var_ren, ← ren_eq_subst, ← ren_eq_subst]

theorem ren_num (ξ : Nat → Nat) (n : Nat) : ren ξ (num n) = num n := by
  rw [ren_eq_subst]; exact subst_num _ n

theorem Par.ren {t t' : Tm} (h : Par f t t') : ∀ ξ : Nat → Nat, Par f (Tm.ren ξ t) (Tm.ren ξ t') := by
  induction h with
  | var n => intro ξ; exact .var _
  | orc => intro ξ; exact .orc
  | lam _ ih => intro ξ; exact .lam (ih _)
  | app _ _ iht ihu => intro ξ; exact .app (iht ξ) (ihu ξ)
  | beta _ _ ihb iha =>
      intro ξ
      rw [ren_beta]
      exact .beta (ihb _) (iha ξ)
  | delta n =>
      intro ξ
      show Par f (Tm.app .orc (Tm.ren ξ (num n))) (Tm.ren ξ (num (f n)))
      rw [ren_num, ren_num]
      exact .delta n

theorem Par.up {σ τ : Nat → Tm} (h : ∀ i, Par f (σ i) (τ i)) : ∀ i, Par f (up σ i) (up τ i)
  | 0 => .var 0
  | i + 1 => (h i).ren Nat.succ

theorem Par.subst {t t' : Tm} (h : Par f t t') :
    ∀ {σ τ : Nat → Tm}, (∀ i, Par f (σ i) (τ i)) → Par f (Tm.subst σ t) (Tm.subst τ t') := by
  induction h with
  | var n => intro σ τ hσ; exact hσ n
  | orc => intro σ τ _; exact .orc
  | lam _ ih => intro σ τ hσ; exact .lam (ih (Par.up hσ))
  | app _ _ iht ihu => intro σ τ hσ; exact .app (iht hσ) (ihu hσ)
  | beta _ _ ihb iha =>
      intro σ τ hσ
      rw [subst_cons_comm]
      exact .beta (ihb (Par.up hσ)) (iha hσ)
  | delta n =>
      intro σ τ _
      show Par f (Tm.app .orc (Tm.subst σ (num n))) (Tm.subst τ (num (f n)))
      rw [subst_num, subst_num]
      exact .delta n

theorem Par.cons {a a' : Tm} (h : Par f a a') : ∀ i, Par f (cons a Tm.var i) (cons a' Tm.var i)
  | 0 => h
  | i + 1 => .var i

/-! ## Numerals are rigid -/

theorem Par.iterApp_inv : ∀ {n : Nat} {u : Tm}, Par f (iterApp n) u → u = iterApp n
  | 0, _, .var _ => rfl
  | n + 1, _, .app h₁ h₂ => by
      cases h₁
      rw [Par.iterApp_inv h₂]
      rfl

theorem Par.num_inv {n : Nat} {u : Tm} (h : Par f (num n) u) : u = num n := by
  cases h with
  | lam h =>
      cases h with
      | lam h => rw [Par.iterApp_inv h]; rfl

/-! ## Complete development -/

/-- The complete development: contract every redex visible in `t` at once. -/
def cd (f : Nat → Nat) : Tm → Tm
  | .var n => .var n
  | .orc => .orc
  | .lam t => .lam (cd f t)
  | .app (.lam b) a => subst (cons (cd f a) var) (cd f b)
  | .app .orc a =>
      match num? a with
      | some n => num (f n)
      | none => .app .orc (cd f a)
  | .app (.var n) a => .app (.var n) (cd f a)
  | .app (.app t₁ t₂) a => .app (cd f (.app t₁ t₂)) (cd f a)

theorem Par.triangle {t u : Tm} (h : Par f t u) : Par f u (cd f t) := by
  induction h with
  | var n => exact .var n
  | orc => exact .orc
  | lam _ ih => exact .lam ih
  | @app t t' a a' ht ha iht iha =>
      cases t with
      | var n =>
          cases ht
          exact .app (.var n) iha
      | orc =>
          cases ht
          show Par f (Tm.app .orc a') (match num? a with
            | some n => num (f n)
            | none => Tm.app .orc (cd f a))
          cases hn : num? a with
          | none => exact .app .orc iha
          | some n =>
              rw [num?_spec hn] at ha
              rw [Par.num_inv ha]
              exact .delta n
      | lam b =>
          cases ht with
          | lam hb =>
              have ihb : Par f (Tm.lam _) (Tm.lam (cd f b)) := iht
              cases ihb with
              | lam ihb => exact .beta ihb iha
      | app t₁ t₂ => exact .app iht iha
  | beta _ _ ihb iha => exact ihb.subst (Par.cons iha)
  | delta n =>
      show Par f (num (f n)) (match num? (num n) with
        | some n => num (f n)
        | none => Tm.app .orc (cd f (num n)))
      rw [num?_num]
      exact Par.refl _

/-! ## The Church–Rosser theorem -/

theorem Par.steps {t u : Tm} (h : Par f t u) : Steps f t u := by
  induction h with
  | var n => exact .refl _
  | orc => exact .refl _
  | lam _ ih => exact ih.lam
  | app _ _ iht ihu => exact Steps.app iht ihu
  | beta _ _ ihb iha =>
      exact (Steps.app (Steps.lam ihb) iha).trans (Steps.beta _ _)
  | delta n => exact Steps.single (Step.delta n)

/-- Strip lemma: a parallel step and a multi-step close up. -/
theorem Par.strip {t u : Tm} (h : Par f t u) {v : Tm} (hv : Steps f t v) :
    ∃ w, Steps f u w ∧ Par f v w := by
  induction hv generalizing u with
  | refl => exact ⟨u, .refl u, h⟩
  | head s _ ih =>
      have h₁ : Par f u (cd f _) := h.triangle
      have h₂ : Par f _ (cd f _) := (Par.of_step s).triangle
      obtain ⟨w, hw₁, hw₂⟩ := ih h₂
      exact ⟨w, h₁.steps.trans hw₁, hw₂⟩

theorem Steps.confluent {t u v : Tm} (hu : Steps f t u) (hv : Steps f t v) :
    ∃ w, Steps f u w ∧ Steps f v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, .refl v⟩
  | head s _ ih =>
      obtain ⟨w₁, hw₁, hp⟩ := (Par.of_step s).strip hv
      obtain ⟨w, hw, hw'⟩ := ih hw₁
      exact ⟨w, hw, hp.steps.trans hw'⟩

/-! ## Normal forms -/

def Normal (f : Nat → Nat) (t : Tm) : Prop := ∀ u, ¬ Step f t u

theorem Steps.eq_of_normal {t u : Tm} (h : Steps f t u) (hn : Normal f t) : u = t := by
  cases h with
  | refl => rfl
  | head s _ => exact absurd s (hn _)

theorem Normal.iterApp : ∀ n, Normal f (iterApp n)
  | 0 => fun _ s => nomatch s
  | n + 1 => fun u s => by
      cases s with
      | appL _ s => exact nomatch s
      | appR _ s => exact Normal.iterApp n _ s

theorem Normal.num (n : Nat) : Normal f (num n) := fun u s => by
  cases s with
  | lam s =>
      cases s with
      | lam s => exact Normal.iterApp n _ s

/-- If the normal-order step function is stuck, no step is possible. -/
theorem normal_of_nstep : ∀ {t : Tm}, nstep f t = none → Normal f t
  | .var _, _ => fun _ s => nomatch s
  | .orc, _ => fun _ s => nomatch s
  | .lam t, h => fun u s => by
      cases ht : nstep f t with
      | some _ => simp [nstep, ht] at h
      | none =>
          cases s with
          | lam s => exact normal_of_nstep ht _ s
  | .app t a, h => fun u s => by
      simp only [nstep] at h
      cases t with
      | lam b => simp [appStep] at h
      | orc =>
          simp only [appStep] at h
          cases hn : num? a with
          | some n => rw [hn] at h; cases h
          | none =>
              rw [hn] at h
              cases ha : nstep f a with
              | some _ => rw [ha] at h; cases h
              | none =>
                  cases s with
                  | delta n => simp [num?_num] at hn
                  | appL _ s => exact nomatch s
                  | appR _ s => exact normal_of_nstep ha _ s
      | var n =>
          simp only [appStep] at h
          cases ha : nstep f a with
          | some _ =>
              have : nstep f (Tm.var n) = none := rfl
              rw [this, ha] at h; cases h
          | none =>
              cases s with
              | appL _ s => exact nomatch s
              | appR _ s => exact normal_of_nstep ha _ s
      | app t₁ t₂ =>
          simp only [appStep] at h
          cases ht : nstep f (Tm.app t₁ t₂) with
          | some _ => rw [ht] at h; cases h
          | none =>
              rw [ht] at h
              cases ha : nstep f a with
              | some _ => rw [ha] at h; cases h
              | none =>
                  cases s with
                  | appL _ s => exact normal_of_nstep ht _ s
                  | appR _ s => exact normal_of_nstep ha _ s

theorem steps_nf (x : SNTm f) : Steps f x.term (nf f x) := by
  obtain ⟨t, h⟩ := x
  induction h with
  | intro t hacc ih =>
      rw [nf]
      split
      · exact .refl _
      · next u hu => exact Steps.head (nstep_sound hu) (ih u (nstep_sound hu))

theorem normal_nf (x : SNTm f) : Normal f (nf f x) := normal_of_nstep (nstep_nf f x)

/-- **The normalizer finds every numeral the program reduces to.** -/
theorem nf_eq_of_steps (x : SNTm f) {n : Nat} (h : Steps f x.term (num n)) : nf f x = num n := by
  obtain ⟨w, h₁, h₂⟩ := Steps.confluent h (steps_nf x)
  rw [h₁.eq_of_normal (Normal.num n)] at h₂
  exact (h₂.eq_of_normal (normal_nf x)).symm

theorem decode_nf_of_steps (x : SNTm f) {n : Nat} (h : Steps f x.term (num n)) :
    decode (nf f x) = n := by
  rw [nf_eq_of_steps x h, decode, num?_num]
  rfl

end BusyLean.F
