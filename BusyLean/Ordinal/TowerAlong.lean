import BusyLean.Ordinal.BuchholzBase

/-!
# Towers along a well-founded index

Contender 22's `tower` iterates `WFO.next` (all level-bounded Buchholz systems
over a base) along the natural numbers. Here the index is any well-founded
order `J`: the stage at `j` is `next` applied to the union of all stages below
`j`, ordered by index first. The union of all stages (`limitAlong J`) is again
a `WFO`, so it can index the next round:

`N 0 = tower 1`, `N (k+1) = limitAlong (N k)`.

Heuristically the stage at `j` has order type `ψ₀(Ω_ω · (j+1))`, so the rounds
climb the fixed points of `x ↦ ψ₀(Ω_ω · x)`.

Everything is computable. The recursion along `J` uses `termination_by` with a
`WellFoundedRelation` built from `J.wf`, not `WellFounded.fix` on data.
-/

namespace BusyLean.Ordinal

open BuchB

namespace BuchB.WFO

/-- Restriction of `J` to the indices below `j`. -/
def sub (J : WFO) (j : J.T) : WFO where
  T := {i : J.T // J.lt i j = true}
  dec := fun a b => if h : a.1 = b.1 then isTrue (Subtype.ext h)
    else isFalse fun e => h (congrArg Subtype.val e)
  lt := fun a b => J.lt a.1 b.1
  trans := fun a b c => J.trans a.1 b.1 c.1
  wf := fun a => by
    obtain ⟨i, hi⟩ := a
    have h := J.wf i
    revert hi
    induction h with
    | intro i _ ih =>
      intro hi
      exact Acc.intro _ fun ⟨i', hi'⟩ hlt => ih i' hlt hi'
  enum := fun n => (J.enum n).filterMap fun i => if h : J.lt i j = true then some ⟨i, h⟩ else none

/-- The union of a family of orders, ordered by index first. -/
def sigma (J : WFO) (F : J.T → WFO) : WFO where
  T := Σ i : J.T, (F i).T
  dec := fun ⟨i, x⟩ ⟨i', x'⟩ =>
    if h : i = i' then by
      subst h
      exact if hx : x = x' then isTrue (hx ▸ rfl)
        else isFalse fun e => hx (eq_of_heq (Sigma.mk.inj e).2)
    else isFalse fun e => h (Sigma.mk.inj e).1
  lt := fun ⟨i, x⟩ ⟨i', x'⟩ =>
    J.lt i i' || (if h : i = i' then (F i').lt (h ▸ x) x' else false)
  trans := by
    intro ⟨i, x⟩ ⟨i', x'⟩ ⟨i'', x''⟩ h₁ h₂
    simp only [Bool.or_eq_true] at h₁ h₂ ⊢
    by_cases e₁ : i = i'
    · subst e₁
      rw [dite_eq_left rfl] at h₁
      have h₁' : J.lt i i = true ∨ (F i).lt x x' = true := h₁
      by_cases e₂ : i = i''
      · subst e₂
        rw [dite_eq_left rfl] at h₂
        have h₂' : J.lt i i = true ∨ (F i).lt x' x'' = true := h₂
        rw [dite_eq_left rfl]
        rcases h₁' with h | h
        · exact Or.inl h
        · rcases h₂' with h' | h'
          · exact Or.inl h'
          · exact Or.inr ((F i).trans x x' x'' h h')
      · rw [dite_eq_right e₂] at h₂ ⊢
        simp only [Bool.false_eq_true, or_false] at h₂ ⊢
        exact h₂
    · rw [dite_eq_right e₁] at h₁
      simp only [Bool.false_eq_true, or_false] at h₁
      by_cases e₂ : i' = i''
      · subst e₂
        left; exact h₁
      · rw [dite_eq_right e₂] at h₂
        simp only [Bool.false_eq_true, or_false] at h₂
        left; exact J.trans i i' i'' h₁ h₂
  wf := by
    intro ⟨i, x⟩
    have hi := J.wf i
    induction hi with
    | intro i _ ihi =>
      have hx := (F i).wf x
      induction hx with
      | intro x _ ihx =>
        refine Acc.intro _ fun ⟨i', x'⟩ hlt => ?_
        simp only [Bool.or_eq_true] at hlt
        by_cases e : i' = i
        · subst e
          rw [dite_eq_left rfl] at hlt
          rcases hlt with h | h
          · exact ihi i' h x'
          · exact ihx x' h
        · rw [dite_eq_right e] at hlt
          simp only [Bool.false_eq_true, or_false] at hlt
          exact ihi i' hlt x'
  enum := fun n => (J.enum n).flatMap fun i => ((F i).enum n).map fun x => ⟨i, x⟩

/-- `J`'s order as a well-founded relation, for recursion along `J`. -/
instance (priority := high) wfRel (J : WFO) : WellFoundedRelation J.T :=
  ⟨fun x y => J.lt x y = true, ⟨J.wf⟩⟩

/-- The stage at `j`: all level-bounded systems over the union of the stages below `j`. -/
def towerAlong (J : WFO) (j : J.T) : WFO :=
  (sigma (sub J j) (fun i => towerAlong J i.1)).next
termination_by j
decreasing_by exact i.2

/-- The union of all stages of the tower along `J`, ordered by index first. -/
def limitAlong (J : WFO) : WFO := sigma J (towerAlong J)

end BuchB.WFO

/-- Rounds of transfinite towers: each round is indexed by the previous one. -/
def roundTower : Nat → BuchB.WFO
  | 0 => tower 1
  | k + 1 => (roundTower k).limitAlong

theorem roundTower_wf (k : Nat) : WellFounded (FL.ALt (α := (roundTower k).T)) :=
  ⟨(roundTower k).wf⟩

end BusyLean.Ordinal
