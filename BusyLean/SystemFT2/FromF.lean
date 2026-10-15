import BusyLean.SystemFT2.Normalize
import BusyLean.SystemF.Normalize

/-!
# System F's terms inside System FT2's

FT2's terms extend System F's untyped terms (variables, λ, application and the
oracle) with tree constructors, a tree recursor and the oracle tree. `embF` is
the inclusion. On included terms the two normal-order steppers agree
(`nstep_embF`): no tree rule fires, and the oracle rule reads the numeric part
of the FT2 oracle. So the FT2 normal form of an included term is the inclusion
of its F normal form (`nf_embF`), and the numbers they denote agree
(`decode_embF`).
-/

namespace BusyLean.FT2

open Tm

/-- The inclusion of System F's terms. -/
def embF : F.Tm → Tm
  | .var n => var n
  | .app t u => app (embF t) (embF u)
  | .lam t => lam (embF t)
  | .orc => orc

theorem embF_ren : ∀ (t : F.Tm) (ξ : Nat → Nat), embF (F.Tm.ren ξ t) = ren ξ (embF t)
  | .var _, _ => rfl
  | .app t u, ξ => by
      show app (embF (F.Tm.ren ξ t)) (embF (F.Tm.ren ξ u)) = app (ren ξ (embF t)) (ren ξ (embF u))
      rw [embF_ren t, embF_ren u]
  | .lam t, ξ => by
      show lam (embF (F.Tm.ren (F.Tm.upRen ξ) t)) = lam (ren (upRen ξ) (embF t))
      rw [embF_ren t]
      congr 2
  | .orc, _ => rfl

theorem embF_subst : ∀ (t : F.Tm) (σ : Nat → F.Tm),
    embF (F.Tm.subst σ t) = subst (fun n => embF (σ n)) (embF t)
  | .var _, _ => rfl
  | .app t u, σ => by
      show app (embF (F.Tm.subst σ t)) (embF (F.Tm.subst σ u)) = _
      rw [embF_subst t, embF_subst u]
      rfl
  | .lam t, σ => by
      show lam (embF (F.Tm.subst (F.Tm.up σ) t)) = lam (subst (up fun n => embF (σ n)) (embF t))
      rw [embF_subst t]
      congr 2
      funext n
      cases n with
      | zero => rfl
      | succ n => exact embF_ren (σ n) Nat.succ
  | .orc, _ => rfl

theorem embF_iterApp : ∀ n : Nat, embF (F.Tm.iterApp n) = iterApp n
  | 0 => rfl
  | n + 1 => by
      show app (var 1) (embF (F.Tm.iterApp n)) = _
      rw [embF_iterApp n]
      rfl

theorem embF_num (n : Nat) : embF (F.Tm.num n) = num n := by
  show lam (lam (embF (F.Tm.iterApp n))) = _
  rw [embF_iterApp]
  rfl

theorem iterApp?_embF : ∀ t : F.Tm, iterApp? (embF t) = F.Tm.iterApp? t
  | .var 0 => rfl
  | .var (_ + 1) => rfl
  | .app (.var 0) _ => rfl
  | .app (.var 1) t => by
      show (iterApp? (embF t)).map Nat.succ = (F.Tm.iterApp? t).map Nat.succ
      rw [iterApp?_embF t]
  | .app (.var (_ + 2)) _ => rfl
  | .app (.app _ _) _ => rfl
  | .app (.lam _) _ => rfl
  | .app .orc _ => rfl
  | .lam _ => rfl
  | .orc => rfl

theorem num?_embF : ∀ t : F.Tm, num? (embF t) = F.Tm.num? t
  | .lam (.lam t) => iterApp?_embF t
  | .lam (.var _) => rfl
  | .lam (.app _ _) => rfl
  | .lam .orc => rfl
  | .var _ => rfl
  | .app _ _ => rfl
  | .orc => rfl

theorem decode_embF (t : F.Tm) : decode (embF t) = F.decode t := by
  unfold decode F.decode
  rw [num?_embF]

/-- No tree redex has an included term at its head. -/
theorem headStep_app_embF (f : Orc) (t₁ t₂ a : F.Tm) :
    headStep f (embF (.app t₁ t₂)) (embF a) = none := by
  cases t₁ with
  | var _ => rfl
  | lam _ => rfl
  | orc => rfl
  | app t₃ _ =>
      cases t₃ with
      | var _ => rfl
      | lam _ => rfl
      | orc => rfl
      | app t₅ _ => cases t₅ <;> rfl

/-- **The normal-order steppers agree on included terms.** -/
theorem nstep_embF (f : Orc) : ∀ t : F.Tm, nstep f (embF t) = (F.nstep f.nat t).map embF
  | .var _ => rfl
  | .orc => rfl
  | .lam t => by
      show (nstep f (embF t)).map lam = ((F.nstep f.nat t).map F.Tm.lam).map embF
      rw [nstep_embF f t]
      cases F.nstep f.nat t <;> rfl
  | .app t a => by
      have ht := nstep_embF f t
      have ha := nstep_embF f a
      show appStep f (embF t) (embF a) (nstep f (embF t)) (nstep f (embF a)) =
        (F.appStep f.nat t a (F.nstep f.nat t) (F.nstep f.nat a)).map embF
      rw [ht, ha]
      cases t with
      | lam b =>
          show some (subst (cons (embF a) var) (embF b)) =
            some (embF (F.Tm.subst (F.Tm.cons a F.Tm.var) b))
          rw [embF_subst]
          congr 2
          funext n
          cases n <;> rfl
      | var n =>
          show ((F.nstep f.nat a).map embF).map (app (var n)) =
            ((F.nstep f.nat a).map (F.Tm.app (F.Tm.var n))).map embF
          cases F.nstep f.nat a <;> rfl
      | orc =>
          show (match (num? (embF a)).map (fun n => num (f.nat n)) with
              | some v => some v
              | none => ((F.nstep f.nat a).map embF).map (app orc)) =
            (match F.Tm.num? a with
              | some n => some (F.Tm.num (f.nat n))
              | none => (F.nstep f.nat a).map (F.Tm.app F.Tm.orc)).map embF
          rw [num?_embF]
          cases F.Tm.num? a with
          | some n =>
              show some (num (f.nat n)) = some (embF (F.Tm.num (f.nat n)))
              rw [embF_num]
          | none => cases F.nstep f.nat a <;> rfl
      | app t₁ t₂ =>
          unfold appStep
          rw [headStep_app_embF]
          show (match (F.nstep f.nat (F.Tm.app t₁ t₂)).map embF with
              | some t' => some (app t' (embF a))
              | none => ((F.nstep f.nat a).map embF).map (app (app (embF t₁) (embF t₂)))) =
            (match F.nstep f.nat (F.Tm.app t₁ t₂) with
              | some t' => some (F.Tm.app t' a)
              | none => (F.nstep f.nat a).map (F.Tm.app (F.Tm.app t₁ t₂))).map embF
          cases F.nstep f.nat (F.Tm.app t₁ t₂) with
          | some t' => rfl
          | none => cases F.nstep f.nat a <;> rfl

/-- One normal-order step does not change the normal form. -/
theorem nf_of_nstep (f : Orc) {t u : Tm} (h : SN f t) (hs : nstep f t = some u) :
    nf f ⟨t, h⟩ = nf f ⟨u, h.step (nstep_sound hs)⟩ := by
  rw [nf]
  split
  · next hn => rw [hs] at hn; cases hn
  · next u' hu' => rw [hs] at hu'; cases hu'; rfl

theorem nf_congr (f : Orc) {t u : Tm} (e : t = u) (h : SN f t) (h' : SN f u) :
    nf f ⟨t, h⟩ = nf f ⟨u, h'⟩ := by
  subst e
  rfl

/-- **The FT2 normal form of an included term is the inclusion of its F normal form.** -/
theorem nf_embF (f : Orc) (x : F.SNTm f.nat) (h' : SN f (embF x.term)) :
    nf f ⟨embF x.term, h'⟩ = embF (F.nf f.nat x) := by
  obtain ⟨t, h⟩ := x
  induction h with
  | intro t _ ih =>
      rw [F.nf]
      split
      · next hn =>
          rw [nf]
          split
          · rfl
          · next u hu => rw [nstep_embF, hn] at hu; cases hu
      · next u hu =>
          have hs : nstep f (embF t) = some (embF u) := by rw [nstep_embF, hu]; rfl
          rw [nf_of_nstep f h' hs]
          exact ih u (F.nstep_sound hu) _

/-! ## Closed terms -/

/-- All variables of `t` are below `k`. -/
def closedB : Nat → Tm → Bool
  | k, var n => decide (n < k)
  | k, app t u => closedB k t && closedB k u
  | k, lam t => closedB (k + 1) t
  | _, orc => true
  | _, con _ => true
  | _, trec => true
  | _, tsub _ => true
  | _, tsubl _ => true

theorem subst_closed : ∀ (t : Tm) {k : Nat} {σ : Nat → Tm}, closedB k t = true →
    (∀ i, i < k → σ i = var i) → subst σ t = t
  | var n, _, _, h, hσ => hσ n (of_decide_eq_true h)
  | app t u, k, σ, h, hσ => by
      simp only [closedB, Bool.and_eq_true] at h
      show app (subst σ t) (subst σ u) = _
      rw [subst_closed t h.1 hσ, subst_closed u h.2 hσ]
  | lam t, k, σ, h, hσ => by
      have hup : ∀ i, i < k + 1 → up σ i = var i := fun i hi => by
        cases i with
        | zero => rfl
        | succ i =>
            show ren Nat.succ (σ i) = var (i + 1)
            rw [hσ i (by omega)]
            rfl
      show lam (subst (up σ) t) = _
      rw [subst_closed t (k := k + 1) h hup]
  | orc, _, _, _, _ => rfl
  | con _, _, _, _, _ => rfl
  | trec, _, _, _, _ => rfl
  | tsub _, _, _, _, _ => rfl
  | tsubl _, _, _, _, _ => rfl

end BusyLean.FT2
