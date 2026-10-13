import BusyLean.SystemF.Syntax

/-!
# Reduction and strong normalization

One-step reduction is full β-reduction plus the oracle rule
`orc n̄ ⟶ f(n)‾` on Church numerals, closed under all contexts.
`SN f t` says that every reduction sequence from `t` is finite (accessibility).
-/

namespace BusyLean.F

open Tm

inductive Step (f : Nat → Nat) : Tm → Tm → Prop where
  | beta (b a : Tm) : Step f (app (lam b) a) (subst (cons a var) b)
  | delta (n : Nat) : Step f (app orc (num n)) (num (f n))
  | appL {t t' : Tm} (u : Tm) : Step f t t' → Step f (app t u) (app t' u)
  | appR (t : Tm) {u u' : Tm} : Step f u u' → Step f (app t u) (app t u')
  | lam {t t' : Tm} : Step f t t' → Step f (lam t) (lam t')

/-- Strong normalization: no infinite reduction sequence starts at `t`. -/
def SN (f : Nat → Nat) (t : Tm) : Prop := Acc (fun u t => Step f t u) t

theorem SN.intro {f : Nat → Nat} {t : Tm} (h : ∀ u, Step f t u → SN f u) : SN f t :=
  Acc.intro t h

theorem SN.step {f : Nat → Nat} {t u : Tm} (h : SN f t) (s : Step f t u) : SN f u :=
  Acc.inv h s

/-! ## Stability under substitution -/

theorem Step.subst {f : Nat → Nat} {t u : Tm} (s : Step f t u) :
    ∀ σ : Nat → Tm, Step f (Tm.subst σ t) (Tm.subst σ u) := by
  induction s with
  | beta b a =>
      intro σ
      rw [subst_cons_comm]
      exact Step.beta _ _
  | delta n =>
      intro σ
      show Step f (app orc (Tm.subst σ (num n))) (Tm.subst σ (num (f n)))
      rw [subst_num, subst_num]
      exact Step.delta n
  | appL u _ ih => intro σ; exact Step.appL _ (ih σ)
  | appR t _ ih => intro σ; exact Step.appR _ (ih σ)
  | lam _ ih => intro σ; exact Step.lam (ih (up σ))

/-! ## Closure properties of SN -/

theorem SN.of_app_left {f : Nat → Nat} {t u : Tm} (h : SN f (app t u)) : SN f t := by
  generalize he : app t u = s at h
  induction h generalizing t with
  | intro s _ ih =>
      subst he
      exact SN.intro fun t' st => ih _ (Step.appL u st) rfl

theorem SN.of_app_right {f : Nat → Nat} {t u : Tm} (h : SN f (app t u)) : SN f u := by
  generalize he : app t u = s at h
  induction h generalizing u with
  | intro s _ ih =>
      subst he
      exact SN.intro fun u' su => ih _ (Step.appR t su) rfl

theorem SN.of_lam {f : Nat → Nat} {t : Tm} (h : SN f (Tm.lam t)) : SN f t := by
  generalize he : Tm.lam t = s at h
  induction h generalizing t with
  | intro s _ ih =>
      subst he
      exact SN.intro fun t' st => ih _ (Step.lam st) rfl

/-- Inversion of a step out of a λ. -/
theorem Step.lam_inv {f : Nat → Nat} {t u : Tm} (s : Step f (Tm.lam t) u) :
    ∃ t', u = Tm.lam t' ∧ Step f t t' := by
  cases s with
  | lam s => exact ⟨_, rfl, s⟩

theorem SN.lam {f : Nat → Nat} {t : Tm} (h : SN f t) : SN f (Tm.lam t) := by
  induction h with
  | intro t _ ih =>
      exact SN.intro fun u s => by
        obtain ⟨t', rfl, s'⟩ := s.lam_inv
        exact ih t' s'

theorem SN.var (f : Nat → Nat) (n : Nat) : SN f (Tm.var n) :=
  SN.intro fun _ s => nomatch s

theorem SN.orc (f : Nat → Nat) : SN f Tm.orc :=
  SN.intro fun _ s => nomatch s

/-- If `t x` is SN for a variable `x`, then so is `t`. -/
theorem SN.of_app_var {f : Nat → Nat} {t : Tm} {n : Nat} (h : SN f (app t (Tm.var n))) :
    SN f t :=
  h.of_app_left

end BusyLean.F
