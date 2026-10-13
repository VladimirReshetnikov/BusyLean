/-!
# Well-foundedness of the lexicographic order on sorted lists

A non-increasing list `[a₁, …, a_k]` denotes the Cantor normal form
`ω^a₁ + ⋯ + ω^a_k`, and the lexicographic order on such lists is the ordinal
order. This file proves that the order is well-founded on sorted lists, assuming
only that the elements are accessible for the (Boolean, decidable) element
order. Transitivity is never used, and asymmetry follows from accessibility.

With natural-number exponents this gives notations for the ordinals below
`ω^ω` (`OmegaPow`); applied hereditarily it gives `ε₀`.

The proof splits a sorted list headed by `h` into a run `h, …, h` (k+1 copies)
and a tail whose head is below `h`. Two such lists compare like the pairs
`(k, tail)`, lexicographically.
-/

namespace BusyLean.Ordinal

variable {β : Type} [DecidableEq β] (lt : β → β → Bool)

/-- Non-strict order: below or equal. -/
def le (a b : β) : Bool := lt a b || decide (a = b)

/-- Non-increasing lists. -/
def sorted : List β → Bool
  | [] => true
  | [_] => true
  | x :: y :: t => le lt y x && sorted (y :: t)

/-- The lexicographic order on lists (a proper prefix is smaller). -/
def llt : List β → List β → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => lt x y || (decide (x = y) && llt xs ys)

/-- The order on sorted lists, as a relation on raw lists. -/
def SR (l' l : List β) : Prop := sorted lt l' = true ∧ llt lt l' l = true

/-- The element order, as a relation. -/
def LT' (a b : β) : Prop := lt a b = true

variable {lt}

omit [DecidableEq β] in
theorem asymm_of_acc {a : β} (ha : Acc (LT' lt) a) : ∀ {b : β}, lt a b = true → lt b a = true → False := by
  induction ha with
  | intro a _ ih => exact fun hab hba => ih _ hba hba hab

omit [DecidableEq β] in
theorem irrefl_of_acc {a : β} (ha : Acc (LT' lt) a) : lt a a = false := by
  cases h : lt a a with
  | false => rfl
  | true => exact (asymm_of_acc ha h h).elim

theorem llt_nil_right (l : List β) : llt lt l [] = false := by
  cases l <;> rfl

theorem acc_nil : Acc (SR lt) [] :=
  Acc.intro _ fun l' h => by have h2 := h.2; rw [llt_nil_right] at h2; cases h2

/-- The tail after a run of `h` lies strictly below `h`. -/
def Below (lt : β → β → Bool) (h : β) (r : List β) : Prop := ∀ y, r.head? = some y → lt y h = true

theorem sorted_tail {x : β} {t : List β} (h : sorted lt (x :: t) = true) : sorted lt t = true := by
  match t, h with
  | [], _ => rfl
  | _ :: _, h => simp only [sorted, Bool.and_eq_true] at h; exact h.2

/-- A sorted list headed by `h` is a run of `h` followed by a tail below `h`. -/
theorem decompose (h : β) : ∀ (l : List β), sorted lt l = true → l.head? = some h →
    ∃ k r, l = List.replicate (k + 1) h ++ r ∧ sorted lt r = true ∧ Below lt h r
  | [], _, e => nomatch e
  | [x], _, e => by
      cases e
      exact ⟨0, [], rfl, rfl, fun _ e => nomatch e⟩
  | x :: y :: t, hs, e => by
      have ex : x = h := Option.some.inj e
      subst ex
      have hst := sorted_tail hs
      simp only [sorted, Bool.and_eq_true, le, Bool.or_eq_true, decide_eq_true_eq] at hs
      rcases hs.1 with hy | hy
      · exact ⟨0, y :: t, rfl, hst, fun z ez => by cases ez; exact hy⟩
      · subst hy
        obtain ⟨k, r, er, hr, hb⟩ := decompose _ _ hst rfl
        exact ⟨k + 1, r, by rw [er]; rfl, hr, hb⟩

/-- Comparing two runs of `h`: the longer run wins, and equal runs compare tails. -/
theorem compare_runs {h : β} (hh : Acc (LT' lt) h) {r r' : List β} (hr : Below lt h r) :
    ∀ (a b : Nat), llt lt (List.replicate a h ++ r') (List.replicate b h ++ r) = true →
      a < b ∨ (a = b ∧ llt lt r' r = true)
  | 0, 0, e => Or.inr ⟨rfl, e⟩
  | 0, _ + 1, _ => Or.inl (Nat.succ_pos _)
  | a + 1, 0, e => by
      match r, hr with
      | [], _ =>
          simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.append_nil] at e
          rw [llt_nil_right] at e; cases e
      | y :: ys, hb =>
          have hyh : lt y h = true := hb y rfl
          simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append, llt,
            Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at e
          rcases e with e | ⟨rfl, _⟩
          · exact (asymm_of_acc hh e hyh).elim
          · rw [irrefl_of_acc hh] at hyh; cases hyh
  | a + 1, b + 1, e => by
      simp only [List.replicate_succ, List.cons_append, llt, irrefl_of_acc hh, Bool.false_or,
        decide_true, Bool.true_and] at e
      rcases compare_runs hh hr a b e with e1 | ⟨hab, e2⟩
      · exact Or.inl (Nat.succ_lt_succ e1)
      · subst hab; exact Or.inr ⟨rfl, e2⟩

theorem lt_head_of_llt {y h : β} {ys t : List β} (e : llt lt (y :: ys) (h :: t) = true) :
    lt y h = true ∨ y = h := by
  simp only [llt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at e
  rcases e with e | ⟨e, _⟩
  · exact Or.inl e
  · exact Or.inr e

/-- Every sorted list headed by an accessible element is accessible. -/
theorem acc_head {h : β} (hh : Acc (LT' lt) h) :
    ∀ (l : List β), sorted lt l = true → l.head? = some h → Acc (SR lt) l := by
  induction hh with
  | intro h hacc ih =>
    have hh : Acc (LT' lt) h := Acc.intro h hacc
    -- sorted lists below `h` are accessible
    have below : ∀ r, sorted lt r = true → Below lt h r → Acc (SR lt) r := by
      intro r hs hb
      match r, hs, hb with
      | [], _, _ => exact acc_nil
      | y :: ys, hs, hb => exact ih y (hb y rfl) (y :: ys) hs rfl
    -- runs of `h` in front of an accessible tail, by strong induction on the run
    have runs : ∀ (k : Nat) (r : List β), Acc (SR lt) r → Below lt h r →
        Acc (SR lt) (List.replicate k h ++ r) := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ihk =>
        intro r hr
        induction hr with
        | intro r hracc ihr =>
          intro hb
          cases k with
          | zero => exact Acc.intro r hracc
          | succ k =>
            refine Acc.intro _ fun l' ⟨hs', e⟩ => ?_
            match l', hs', e with
            | [], _, _ => exact acc_nil
            | y :: ys, hs', e =>
              rcases lt_head_of_llt (t := List.replicate k h ++ r) e with hy | hy
              · exact ih y hy (y :: ys) hs' rfl
              · subst hy
                obtain ⟨k', r', er', hr', hb'⟩ := decompose y (y :: ys) hs' rfl
                rw [er'] at e ⊢
                rcases compare_runs hh hb (k' + 1) (k + 1) e with hk | ⟨hk, hl⟩
                · exact ihk (k' + 1) hk r' (below r' hr' hb') hb'
                · cases hk
                  exact ihr r' ⟨hr', hl⟩ hb'
    intro l hs e
    obtain ⟨k, r, er, hr, hb⟩ := decompose h l hs e
    rw [er]
    exact runs (k + 1) r (below r hr hb) hb

/-- **Well-foundedness**: if every element is accessible, so is every sorted list. -/
theorem acc_sorted (hwf : ∀ a : β, Acc (LT' lt) a) :
    ∀ l : List β, sorted lt l = true → Acc (SR lt) l
  | [], _ => acc_nil
  | h :: t, hs => acc_head (hwf h) (h :: t) hs rfl

/-- The same, for the subtype of sorted lists. -/
theorem wf_sorted (hwf : ∀ a : β, Acc (LT' lt) a) :
    WellFounded (fun (a b : {l : List β // sorted lt l = true}) => llt lt a.1 b.1 = true) := by
  refine ⟨fun a => ?_⟩
  have h := acc_sorted hwf a.1 a.2
  obtain ⟨l, hl⟩ := a
  simp only at h
  induction h with
  | intro l _ ih =>
    exact Acc.intro _ fun b hb => by
      obtain ⟨l', hl'⟩ := b
      exact ih l' ⟨hl', hb⟩ hl'

end BusyLean.Ordinal
