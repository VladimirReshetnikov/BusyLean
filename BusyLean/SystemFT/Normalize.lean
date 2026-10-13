import BusyLean.SystemFT.Reduction

/-!
# A total normalizer for strongly normalizing terms

`nstep` performs one normal-order (leftmost-outermost) step. The oracle rule
fires once the argument of `orc` is a canonical numeral. Every `nstep` is a
`Step`, so on SN terms the iteration terminates. `nf` is defined by
well-founded recursion on the accessibility proof. The compiler runs it as an
ordinary loop, and the SN theorem certifies that it is total.
-/

namespace BusyLean.FT

open Tm

/-- Normal-order step at an application node, given the steps of its parts. -/
def appStep (f : Nat → Nat) (t a : Tm) (st sa : Option Tm) : Option Tm :=
  match t with
  | .lam b => some (subst (cons a .var) b)
  | .orc =>
      match num? a with
      | some n => some (num (f n))
      | none => sa.map (.app .orc)
  | .var n =>
      match st with
      | some t' => some (.app t' a)
      | none => sa.map (.app (.var n))
  | .app t₁ t₂ =>
      match st with
      | some t' => some (.app t' a)
      | none => sa.map (.app (.app t₁ t₂))
  | .con k => sa.map (.app (.con k))

/-- One normal-order reduction step, or `none` at a normal form. -/
def nstep (f : Nat → Nat) : Tm → Option Tm
  | .var _ => none
  | .orc => none
  | .con _ => none
  | .lam t => (nstep f t).map .lam
  | .app t a => appStep f t a (nstep f t) (nstep f a)

theorem appStep_sound {f : Nat → Nat} {t a v : Tm} {st sa : Option Tm}
    (ht : ∀ u, st = some u → Step f t u) (ha : ∀ u, sa = some u → Step f a u)
    (h : appStep f t a st sa = some v) : Step f (.app t a) v := by
  cases t with
  | lam b =>
      cases h
      exact Step.beta b a
  | orc =>
      simp only [appStep] at h
      cases hn : num? a with
      | some n =>
          rw [hn] at h
          cases h
          rw [num?_spec hn]
          exact Step.delta n
      | none =>
          rw [hn] at h
          cases hsa : sa with
          | none => rw [hsa] at h; cases h
          | some a' =>
              rw [hsa] at h
              cases h
              exact Step.appR _ (ha a' hsa)
  | con k =>
      simp only [appStep] at h
      cases hsa : sa with
      | none => rw [hsa] at h; cases h
      | some a' =>
          rw [hsa] at h; cases h
          exact Step.appR _ (ha a' hsa)
  | var n =>
      simp only [appStep] at h
      cases hst : st with
      | some t' =>
          rw [hst] at h; cases h
          exact Step.appL _ (ht t' hst)
      | none =>
          rw [hst] at h
          cases hsa : sa with
          | none => rw [hsa] at h; cases h
          | some a' =>
              rw [hsa] at h; cases h
              exact Step.appR _ (ha a' hsa)
  | app t₁ t₂ =>
      simp only [appStep] at h
      cases hst : st with
      | some t' =>
          rw [hst] at h; cases h
          exact Step.appL _ (ht t' hst)
      | none =>
          rw [hst] at h
          cases hsa : sa with
          | none => rw [hsa] at h; cases h
          | some a' =>
              rw [hsa] at h; cases h
              exact Step.appR _ (ha a' hsa)

theorem nstep_sound {f : Nat → Nat} : ∀ {t u : Tm}, nstep f t = some u → Step f t u
  | .var _, _, h => nomatch h
  | .orc, _, h => nomatch h
  | .con _, _, h => nomatch h
  | .lam t, u, h => by
      simp only [nstep] at h
      cases ht : nstep f t with
      | none => rw [ht] at h; cases h
      | some t' =>
          rw [ht] at h; cases h
          exact Step.lam (nstep_sound ht)
  | .app t a, _, h =>
      appStep_sound (fun _ e => nstep_sound e) (fun _ e => nstep_sound e) h

/-- A term bundled with a proof that it is strongly normalizing. -/
structure SNTm (f : Nat → Nat) where
  term : Tm
  sn : SN f term

instance (f : Nat → Nat) : WellFoundedRelation (SNTm f) where
  rel x y := Step f y.term x.term
  wf := ⟨fun ⟨t, h⟩ => by
    induction h with
    | intro t _ ih => exact Acc.intro _ fun ⟨u, _⟩ s => ih u s⟩

/-- The normal form of a strongly normalizing term (normal-order strategy). -/
def nf (f : Nat → Nat) (x : SNTm f) : Tm :=
  match h : nstep f x.term with
  | none => x.term
  | some u => nf f ⟨u, x.sn.step (nstep_sound h)⟩
termination_by x
decreasing_by exact nstep_sound h

/-- The result of `nf` admits no further normal-order step. -/
theorem nstep_nf (f : Nat → Nat) (x : SNTm f) : nstep f (nf f x) = none := by
  obtain ⟨t, h⟩ := x
  induction h with
  | intro t hacc ih =>
      rw [nf]
      split
      · assumption
      · next u hu => exact ih u (nstep_sound hu)

/-- The number a normal form denotes: its value as a Church numeral, else `0`. -/
def decode (t : Tm) : Nat := (num? t).getD 0

end BusyLean.FT
