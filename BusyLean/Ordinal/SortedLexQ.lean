import BusyLean.Ordinal.SortedLex

/-!
# Sorted lists over a good part

A variant of `SortedLex` where the elements are restricted by a predicate `Q`
(a `Prop`, typically "accessible"). The relations only compare good elements
and lists of good elements. If every good element is accessible, every sorted
list of good elements is accessible. Used for the argument arrays of the large
Veblen notation, whose entries are only known to be good when their position
and value are accessible.
-/

namespace BusyLean.Ordinal

variable {β : Type} [DecidableEq β] {lt : β → β → Bool} {Q : β → Prop}

/-- The element order on good elements. -/
def LTQ (Q : β → Prop) (lt : β → β → Bool) (a b : β) : Prop := Q a ∧ lt a b = true

/-- The order on sorted lists of good elements. -/
def SRQ (Q : β → Prop) (lt : β → β → Bool) (l' l : List β) : Prop :=
  (∀ x ∈ l', Q x) ∧ sorted lt l' = true ∧ llt lt l' l = true

omit [DecidableEq β] in
theorem asymmQ : ∀ {a : β}, Acc (LTQ Q lt) a → Q a → ∀ {b : β}, Q b →
    lt a b = true → lt b a = true → False := by
  intro a ha
  induction ha with
  | intro a _ ih => exact fun qa b qb hab hba => ih b ⟨qb, hba⟩ qb qa hba hab

omit [DecidableEq β] in
theorem irreflQ {a : β} (ha : Acc (LTQ Q lt) a) (qa : Q a) : lt a a = false := by
  cases h : lt a a with
  | false => rfl
  | true => exact (asymmQ ha qa qa h h).elim

theorem accQ_nil : Acc (SRQ Q lt) [] :=
  Acc.intro _ fun l' h => by have h2 := h.2.2; rw [llt_nil_right] at h2; cases h2

theorem compare_runsQ {h : β} (hh : Acc (LTQ Q lt) h) (qh : Q h) {r r' : List β}
    (hr : Below lt h r) (hrq : ∀ x ∈ r, Q x) :
    ∀ (a b : Nat), llt lt (List.replicate a h ++ r') (List.replicate b h ++ r) = true →
      a < b ∨ (a = b ∧ llt lt r' r = true)
  | 0, 0, e => Or.inr ⟨rfl, e⟩
  | 0, _ + 1, _ => Or.inl (Nat.succ_pos _)
  | a + 1, 0, e => by
      match r, hr, hrq with
      | [], _, _ =>
          simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.append_nil] at e
          rw [llt_nil_right] at e; cases e
      | y :: ys, hb, hrq =>
          have hyh : lt y h = true := hb y rfl
          simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append, llt,
            Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at e
          rcases e with e | ⟨rfl, _⟩
          · exact (asymmQ hh qh (hrq y List.mem_cons_self) e hyh).elim
          · rw [irreflQ hh qh] at hyh; cases hyh
  | a + 1, b + 1, e => by
      simp only [List.replicate_succ, List.cons_append, llt, irreflQ hh qh, Bool.false_or,
        decide_true, Bool.true_and] at e
      rcases compare_runsQ hh qh hr hrq a b e with e1 | ⟨hab, e2⟩
      · exact Or.inl (Nat.succ_lt_succ e1)
      · subst hab; exact Or.inr ⟨rfl, e2⟩

omit [DecidableEq β] in
theorem mem_of_mem_append_right {x : β} {l r : List β} (h : x ∈ r) : x ∈ l ++ r :=
  List.mem_append.2 (Or.inr h)

/-- Every sorted list of good elements headed by an accessible good `h` is accessible. -/
theorem accQ_head_of_acc {h : β} (hh : Acc (LTQ Q lt) h) (qh : Q h) :
    ∀ (l : List β), (∀ x ∈ l, Q x) → sorted lt l = true → l.head? = some h → Acc (SRQ Q lt) l := by
  induction hh with
  | intro h hacc' ih =>
    have hh : Acc (LTQ Q lt) h := Acc.intro h hacc'
    have below : ∀ r, (∀ x ∈ r, Q x) → sorted lt r = true → Below lt h r → Acc (SRQ Q lt) r := by
      intro r hq hs hb
      match r, hq, hs, hb with
      | [], _, _, _ => exact accQ_nil
      | y :: ys, hq, hs, hb =>
          have qy := hq y List.mem_cons_self
          exact ih y ⟨qy, hb y rfl⟩ qy (y :: ys) hq hs rfl
    have runs : ∀ (k : Nat) (r : List β), Acc (SRQ Q lt) r → (∀ x ∈ r, Q x) → Below lt h r →
        Acc (SRQ Q lt) (List.replicate k h ++ r) := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ihk =>
        intro r hr
        induction hr with
        | intro r hracc ihr =>
          intro hrq hb
          cases k with
          | zero => exact Acc.intro r hracc
          | succ k =>
            refine Acc.intro _ fun l' ⟨hq', hs', e⟩ => ?_
            match l', hq', hs', e with
            | [], _, _, _ => exact accQ_nil
            | y :: ys, hq', hs', e =>
              have qy := hq' y List.mem_cons_self
              rcases lt_head_of_llt (t := List.replicate k h ++ r) e with hy | hy
              · exact ih y ⟨qy, hy⟩ qy (y :: ys) hq' hs' rfl
              · subst hy
                obtain ⟨k', r', er', hr', hb'⟩ := decompose y (y :: ys) hs' rfl
                have hq'' : ∀ x ∈ r', Q x := fun x hx => hq' x (by rw [er']; exact mem_of_mem_append_right hx)
                rw [er'] at e ⊢
                rcases compare_runsQ hh qy hb hrq (k' + 1) (k + 1) e with hk | ⟨hk, hl⟩
                · exact ihk (k' + 1) hk r' (below r' hq'' hr' hb') hq'' hb'
                · cases hk
                  exact ihr r' ⟨hq'', hr', hl⟩ hq'' hb'
    intro l hq hs e
    obtain ⟨k, r, er, hr, hb⟩ := decompose h l hs e
    have hrq : ∀ x ∈ r, Q x := fun x hx => hq x (by rw [er]; exact mem_of_mem_append_right hx)
    rw [er]
    exact runs (k + 1) r (below r hrq hr hb) hrq hb

/-- Every sorted list of good elements headed by `h` is accessible. -/
theorem accQ_head (hacc : ∀ a, Q a → Acc (LTQ Q lt) a) {h : β} (qh : Q h) :
    ∀ (l : List β), (∀ x ∈ l, Q x) → sorted lt l = true → l.head? = some h → Acc (SRQ Q lt) l :=
  accQ_head_of_acc (hacc h qh) qh

/-- If every good element is accessible, so is every sorted list of good elements. -/
theorem accQ_sorted (hacc : ∀ a, Q a → Acc (LTQ Q lt) a) :
    ∀ l : List β, (∀ x ∈ l, Q x) → sorted lt l = true → Acc (SRQ Q lt) l
  | [], _, _ => accQ_nil
  | h :: t, hq, hs => accQ_head hacc (hq h List.mem_cons_self) (h :: t) hq hs rfl

end BusyLean.Ordinal
