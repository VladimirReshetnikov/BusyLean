import BusyLean.SystemFT2.Reduction

/-!
# A total normalizer for strongly normalizing terms

`nstep` performs one normal-order (leftmost-outermost) step. The oracle rule
fires once the argument of `orc` is a canonical numeral. Every `nstep` is a
`Step`, so on SN terms the iteration terminates. `nf` is defined by
well-founded recursion on the accessibility proof. The compiler runs it as an
ordinary loop, and the SN theorem certifies that it is total.
-/

namespace BusyLean.FT2

open Tm

/-- Contraction of a `trec` redex `trec z s l a`, if `a` is in constructor form. -/
def iota? (z s l a : Tm) : Option Tm :=
  match a with
  | .con 0 => some z
  | .app (.con 1) b => some (.app s (trecApp z s l b))
  | .app (.con 2) g => some (.app l (.lam (trecApp (ren Nat.succ z) (ren Nat.succ s)
      (ren Nat.succ l) (.app (ren Nat.succ g) (.var 0)))))
  | _ => none

/-- Contraction of `t a` at its head, if it is a redex. -/
def headStep (f : Orc) (t a : Tm) : Option Tm :=
  match t with
  | .lam b => some (subst (cons a .var) b)
  | .orc => (num? a).map fun n => num (f.nat n)
  | .tsubl p => (num? a).map fun k => .tsub (k :: p)
  | .app (.app (.app .trec z) s) l => iota? z s l a
  | _ => none

/-- Normal-order step at an application node, given the steps of its parts. -/
def appStep (f : Orc) (t a : Tm) (st sa : Option Tm) : Option Tm :=
  match headStep f t a with
  | some v => some v
  | none =>
      match st with
      | some t' => some (.app t' a)
      | none => sa.map (.app t)

/-- One normal-order reduction step, or `none` at a normal form. -/
def nstep (f : Orc) : Tm → Option Tm
  | .var _ => none
  | .orc => none
  | .con _ => none
  | .trec => none
  | .tsubl _ => none
  | .tsub p => some (unfoldAt f.tree p)
  | .lam t => (nstep f t).map .lam
  | .app t a => appStep f t a (nstep f t) (nstep f a)

theorem iota?_sound {f : Orc} {z s l a v : Tm} (h : iota? z s l a = some v) :
    Step f (trecApp z s l a) v := by
  unfold iota? at h
  split at h <;> cases h
  · exact Step.iota0 _ _ _
  · exact Step.iota1 _ _ _ _
  · exact Step.iota2 _ _ _ _

theorem headStep_sound {f : Orc} {t a v : Tm} (h : headStep f t a = some v) :
    Step f (.app t a) v := by
  unfold headStep at h
  split at h
  · cases h; exact Step.beta _ _
  · cases hn : num? a with
    | none => rw [hn] at h; cases h
    | some n =>
        rw [hn] at h; cases h
        rw [num?_spec hn]
        exact Step.delta n
  · cases hn : num? a with
    | none => rw [hn] at h; cases h
    | some k =>
        rw [hn] at h; cases h
        rw [num?_spec hn]
        exact Step.branch _ k
  · exact iota?_sound h
  · cases h

theorem appStep_sound {f : Orc} {t a v : Tm} {st sa : Option Tm}
    (ht : ∀ u, st = some u → Step f t u) (ha : ∀ u, sa = some u → Step f a u)
    (h : appStep f t a st sa = some v) : Step f (.app t a) v := by
  unfold appStep at h
  split at h
  · next v' hv => cases h; exact headStep_sound hv
  · cases hst : st with
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

theorem nstep_sound {f : Orc} : ∀ {t u : Tm}, nstep f t = some u → Step f t u
  | .var _, _, h => nomatch h
  | .orc, _, h => nomatch h
  | .con _, _, h => nomatch h
  | .trec, _, h => nomatch h
  | .tsubl _, _, h => nomatch h
  | .tsub p, _, h => by cases h; exact Step.unfold p
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
structure SNTm (f : Orc) where
  term : Tm
  sn : SN f term

instance (f : Orc) : WellFoundedRelation (SNTm f) where
  rel x y := Step f y.term x.term
  wf := ⟨fun ⟨t, h⟩ => by
    induction h with
    | intro t _ ih => exact Acc.intro _ fun ⟨u, _⟩ s => ih u s⟩

/-- The normal form of a strongly normalizing term (normal-order strategy). -/
def nf (f : Orc) (x : SNTm f) : Tm :=
  match h : nstep f x.term with
  | none => x.term
  | some u => nf f ⟨u, x.sn.step (nstep_sound h)⟩
termination_by x
decreasing_by exact nstep_sound h

/-- The result of `nf` admits no further normal-order step. -/
theorem nstep_nf (f : Orc) (x : SNTm f) : nstep f (nf f x) = none := by
  obtain ⟨t, h⟩ := x
  induction h with
  | intro t hacc ih =>
      rw [nf]
      split
      · assumption
      · next u hu => exact ih u (nstep_sound hu)

/-- The number a normal form denotes: its value as a Church numeral, else `0`. -/
def decode (t : Tm) : Nat := (num? t).getD 0

end BusyLean.FT2
