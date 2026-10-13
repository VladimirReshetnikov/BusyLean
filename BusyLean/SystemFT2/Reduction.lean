import BusyLean.SystemFT2.Syntax
import BusyLean.Ordinal.TreeAddress

/-!
# Reduction and strong normalization

One-step reduction is full β-reduction plus the oracle rule
`orc n̄ ⟶ f(n)‾` on Church numerals, closed under all contexts. System FT2 adds:

* the tree recursor: `trec z s l (con 0) ⟶ z`, `trec z s l (con 1 b) ⟶
  s (trec z s l b)`, and `trec z s l (con 2 g) ⟶ l (λk. trec z s l (g k))`;
* the oracle tree `f.tree`, read lazily: `tsub p` unfolds the node at path `p`
  into constructor form, and `tsubl p k̄ ⟶ tsub (k :: p)` gives the branches of a
  limit node.

`SN f t` says that every reduction sequence from `t` is finite (accessibility).
-/

namespace BusyLean.FT2

open Tm Ordinal

/-- The oracles: a number function and a tree. -/
structure Orc where
  nat : Nat → Nat
  tree : CTree

/-- The node of `T` at a path (innermost index first); `zero` off the tree. -/
def nodeAt (T : CTree) : List Nat → CTree
  | [] => T
  | i :: p =>
      match nodeAt T p with
      | .succ t => t
      | .lim g => g i
      | _ => .zero

/-- One unfolding of the oracle tree's node at `p` into constructor form. -/
def unfoldAt (T : CTree) (p : List Nat) : Tm :=
  match nodeAt T p with
  | .succ _ => app (con 1) (tsub (0 :: p))
  | .lim _ => app (con 2) (tsubl p)
  | _ => con 0

/-- `trec z s l u`. -/
def trecApp (z s l u : Tm) : Tm := app (app (app (app trec z) s) l) u

inductive Step (f : Orc) : Tm → Tm → Prop where
  | beta (b a : Tm) : Step f (app (lam b) a) (subst (cons a var) b)
  | delta (n : Nat) : Step f (app orc (num n)) (num (f.nat n))
  | iota0 (z s l : Tm) : Step f (trecApp z s l (con 0)) z
  | iota1 (z s l b : Tm) : Step f (trecApp z s l (app (con 1) b)) (app s (trecApp z s l b))
  | iota2 (z s l g : Tm) : Step f (trecApp z s l (app (con 2) g))
      (app l (lam (trecApp (ren Nat.succ z) (ren Nat.succ s) (ren Nat.succ l)
        (app (ren Nat.succ g) (var 0)))))
  | unfold (p : List Nat) : Step f (tsub p) (unfoldAt f.tree p)
  | branch (p : List Nat) (k : Nat) : Step f (app (tsubl p) (num k)) (tsub (k :: p))
  | appL {t t' : Tm} (u : Tm) : Step f t t' → Step f (app t u) (app t' u)
  | appR (t : Tm) {u u' : Tm} : Step f u u' → Step f (app t u) (app t u')
  | lam {t t' : Tm} : Step f t t' → Step f (lam t) (lam t')

/-- Strong normalization: no infinite reduction sequence starts at `t`. -/
def SN (f : Orc) (t : Tm) : Prop := Acc (fun u t => Step f t u) t

theorem SN.intro {f : Orc} {t : Tm} (h : ∀ u, Step f t u → SN f u) : SN f t :=
  Acc.intro t h

theorem SN.step {f : Orc} {t u : Tm} (h : SN f t) (s : Step f t u) : SN f u :=
  Acc.inv h s

/-! ## Stability under substitution -/

theorem subst_up_shift (σ : Nat → Tm) (t : Tm) :
    Tm.subst (up σ) (ren Nat.succ t) = ren Nat.succ (Tm.subst σ t) := by
  rw [subst_ren, ren_subst]
  rfl

theorem subst_unfoldAt (σ : Nat → Tm) (T : CTree) (p : List Nat) :
    Tm.subst σ (unfoldAt T p) = unfoldAt T p := by
  unfold unfoldAt
  split <;> rfl

theorem Step.subst {f : Orc} {t u : Tm} (s : Step f t u) :
    ∀ σ : Nat → Tm, Step f (Tm.subst σ t) (Tm.subst σ u) := by
  induction s with
  | beta b a =>
      intro σ
      rw [subst_cons_comm]
      exact Step.beta _ _
  | delta n =>
      intro σ
      show Step f (app orc (Tm.subst σ (num n))) (Tm.subst σ (num (f.nat n)))
      rw [subst_num, subst_num]
      exact Step.delta n
  | iota0 z s l => intro σ; exact Step.iota0 _ _ _
  | iota1 z s l b => intro σ; exact Step.iota1 _ _ _ _
  | iota2 z s l g =>
      intro σ
      show Step f (trecApp (Tm.subst σ z) (Tm.subst σ s) (Tm.subst σ l)
        (app (con 2) (Tm.subst σ g))) (app (Tm.subst σ l) (Tm.lam (trecApp
          (Tm.subst (up σ) (ren Nat.succ z)) (Tm.subst (up σ) (ren Nat.succ s))
          (Tm.subst (up σ) (ren Nat.succ l)) (app (Tm.subst (up σ) (ren Nat.succ g)) (var 0)))))
      rw [subst_up_shift, subst_up_shift, subst_up_shift, subst_up_shift]
      exact Step.iota2 _ _ _ _
  | unfold p =>
      intro σ
      show Step f (tsub p) (Tm.subst σ (unfoldAt f.tree p))
      rw [subst_unfoldAt]
      exact Step.unfold p
  | branch p k =>
      intro σ
      show Step f (app (tsubl p) (Tm.subst σ (num k))) (tsub (k :: p))
      rw [subst_num]
      exact Step.branch p k
  | appL u _ ih => intro σ; exact Step.appL _ (ih σ)
  | appR t _ ih => intro σ; exact Step.appR _ (ih σ)
  | lam _ ih => intro σ; exact Step.lam (ih (up σ))

/-! ## Closure properties of SN -/

theorem SN.of_app_left {f : Orc} {t u : Tm} (h : SN f (app t u)) : SN f t := by
  generalize he : app t u = s at h
  induction h generalizing t with
  | intro s _ ih =>
      subst he
      exact SN.intro fun t' st => ih _ (Step.appL u st) rfl

theorem SN.of_app_right {f : Orc} {t u : Tm} (h : SN f (app t u)) : SN f u := by
  generalize he : app t u = s at h
  induction h generalizing u with
  | intro s _ ih =>
      subst he
      exact SN.intro fun u' su => ih _ (Step.appR t su) rfl

theorem SN.of_lam {f : Orc} {t : Tm} (h : SN f (Tm.lam t)) : SN f t := by
  generalize he : Tm.lam t = s at h
  induction h generalizing t with
  | intro s _ ih =>
      subst he
      exact SN.intro fun t' st => ih _ (Step.lam st) rfl

/-- Inversion of a step out of a λ. -/
theorem Step.lam_inv {f : Orc} {t u : Tm} (s : Step f (Tm.lam t) u) :
    ∃ t', u = Tm.lam t' ∧ Step f t t' := by
  cases s with
  | lam s => exact ⟨_, rfl, s⟩

theorem SN.lam {f : Orc} {t : Tm} (h : SN f t) : SN f (Tm.lam t) := by
  induction h with
  | intro t _ ih =>
      exact SN.intro fun u s => by
        obtain ⟨t', rfl, s'⟩ := s.lam_inv
        exact ih t' s'

theorem SN.var (f : Orc) (n : Nat) : SN f (Tm.var n) :=
  SN.intro fun _ s => nomatch s

theorem SN.orc (f : Orc) : SN f Tm.orc :=
  SN.intro fun _ s => nomatch s

theorem SN.con (f : Orc) (k : Nat) : SN f (Tm.con k) :=
  SN.intro fun _ s => nomatch s

/-- If `t x` is SN for a variable `x`, then so is `t`. -/
theorem SN.of_app_var {f : Orc} {t : Tm} {n : Nat} (h : SN f (app t (Tm.var n))) :
    SN f t :=
  h.of_app_left

end BusyLean.FT2
