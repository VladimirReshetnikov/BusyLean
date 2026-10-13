import Baseline

/-! Constructive completeness of the original depth-bounded enumerators. -/

namespace Biggest

theorem ofMemMap {α β : Type} (f : α → β) (xs : List α) (y : β)
    (h : y ∈ xs.map f) : ∃ x, x ∈ xs ∧ f x = y := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
      cases h with
      | head => exact ⟨a, List.Mem.head _, rfl⟩
      | tail _ ht =>
          obtain ⟨x, hx, heq⟩ := ih ht
          exact ⟨x, List.Mem.tail a hx, heq⟩

theorem ofMemAppend {α : Type} {x : α} {xs ys : List α}
    (h : x ∈ xs ++ ys) : x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => exact Or.inr h
  | cons a xs ih =>
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ ht =>
          cases ih ht with
          | inl hx => exact Or.inl (List.Mem.tail a hx)
          | inr hy => exact Or.inr hy

theorem mem_listProd {α β : Type} (a : α) (b : β) (xs : List α) (ys : List β)
    (ha : a ∈ xs) (hb : b ∈ ys) : (a, b) ∈ listProd xs ys := by
  induction ha with
  | head xs =>
      exact memAppendLeft _ (memMap (fun y => (a, y)) hb)
  | tail x _ ih => exact memAppendRight _ ih

theorem ofMemListProd {α β : Type} {x : α} {y : β} {xs : List α} {ys : List β}
    (h : (x, y) ∈ listProd xs ys) : x ∈ xs ∧ y ∈ ys := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
      cases ofMemAppend h with
      | inl hm =>
          obtain ⟨b, hb, heq⟩ := ofMemMap (fun b => (a, b)) ys (x, y) hm
          have hx : a = x := congrArg Prod.fst heq
          have hy : b = y := congrArg Prod.snd heq
          cases hx
          cases hy
          exact ⟨List.Mem.head _, hb⟩
      | inr ht => exact ⟨List.Mem.tail a (ih ht).1, (ih ht).2⟩

theorem typesUpTo_complete (n : Nat) (t : Ty) (h : typeDepth t ≤ n) :
    t ∈ typesUpTo n := by
  induction n generalizing t with
  | zero => exact False.elim ((Nat.not_lt_of_ge h) (typeDepth_pos t))
  | succ n ih =>
      cases t with
      | nat => exact List.Mem.head _
      | arr a b =>
          have hab : max (typeDepth a) (typeDepth b) ≤ n :=
            Nat.le_of_succ_le_succ h
          have ha : a ∈ typesUpTo n :=
            ih a (Nat.le_trans (leMaxLeft _ _) hab)
          have hb : b ∈ typesUpTo n :=
            ih b (Nat.le_trans (leMaxRight _ _) hab)
          exact List.Mem.tail Ty.nat
            (memMap (fun (a, b) => Ty.arr a b) (mem_listProd a b _ _ ha hb))

theorem natsUpTo_complete (n x : Nat) (h : natDepth x ≤ n) :
    x ∈ natsUpTo n := by
  induction n with
  | zero => exact False.elim (Nat.not_succ_le_zero x h)
  | succ n ih =>
      have hx : x ≤ n := Nat.le_of_succ_le_succ h
      cases Nat.lt_or_eq_of_le hx with
      | inl hlt => exact List.Mem.tail n (ih hlt)
      | inr heq =>
          subst x
          exact List.Mem.head _

theorem typesUpTo_sound (n : Nat) (t : Ty) (h : t ∈ typesUpTo n) :
    typeDepth t ≤ n := by
  induction n generalizing t with
  | zero => cases h
  | succ n ih =>
      cases h with
      | head => exact Nat.succ_le_succ (Nat.zero_le n)
      | tail _ hm =>
          obtain ⟨⟨a, b⟩, hp, heq⟩ :=
            ofMemMap (fun (a, b) => Ty.arr a b) _ t hm
          cases heq
          have hp' := ofMemListProd hp
          exact Nat.succ_le_succ (maxLe (ih a hp'.1) (ih b hp'.2))

theorem natsUpTo_sound (n x : Nat) (h : x ∈ natsUpTo n) :
    natDepth x ≤ n := by
  induction n with
  | zero => cases h
  | succ n ih =>
      cases h with
      | head => exact Nat.le_refl _
      | tail _ ht => exact Nat.le_step (ih ht)

theorem termsUpTo_complete (n : Nat) (t : Term) (h : termDepth t ≤ n) :
    t ∈ termsUpTo n := by
  induction n generalizing t with
  | zero => exact False.elim ((Nat.not_lt_of_ge h) (termDepth_pos t))
  | succ n ih =>
      cases t with
      | var x =>
          apply memAppendLeft
          exact memMap Term.var
            (natsUpTo_complete n x (Nat.le_of_succ_le_succ h))
      | lam a b body =>
          have hm : max (max (typeDepth a) (typeDepth b)) (termDepth body) ≤ n :=
            Nat.le_of_succ_le_succ h
          have hab : max (typeDepth a) (typeDepth b) ≤ n :=
            Nat.le_trans (leMaxLeft _ _) hm
          have ha : a ∈ typesUpTo n :=
            typesUpTo_complete n a (Nat.le_trans (leMaxLeft _ _) hab)
          have hb : b ∈ typesUpTo n :=
            typesUpTo_complete n b (Nat.le_trans (leMaxRight _ _) hab)
          have hbody : body ∈ termsUpTo n :=
            ih body (Nat.le_trans (leMaxRight _ _) hm)
          apply memAppendRight
          apply memAppendLeft
          exact memMap (fun ((a, b), body) => Term.lam a b body)
            (mem_listProd (a, b) body _ _ (mem_listProd a b _ _ ha hb) hbody)
      | app f x =>
          have hm : max (termDepth f) (termDepth x) ≤ n :=
            Nat.le_of_succ_le_succ h
          have hf : f ∈ termsUpTo n :=
            ih f (Nat.le_trans (leMaxLeft _ _) hm)
          have hx : x ∈ termsUpTo n :=
            ih x (Nat.le_trans (leMaxRight _ _) hm)
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact memMap (fun (f, x) => Term.app f x) (mem_listProd f x _ _ hf hx)
      | zero =>
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact List.Mem.head []
      | succ =>
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact List.Mem.head []
      | natRec r =>
          have hr : r ∈ typesUpTo n :=
            typesUpTo_complete n r (Nat.le_of_succ_le_succ h)
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          exact memMap Term.natRec hr

theorem eval_le_baseline (t : Term) (n : Nat) (h : termDepth t ≤ n) :
    eval t ≤ baseline n := by
  rw [baseline_eq_maximum]
  exact le_maximum_of_mem eval t (termsUpTo n) (termsUpTo_complete n t h)

theorem termsUpTo_sound (n : Nat) (t : Term) (h : t ∈ termsUpTo n) :
    termDepth t ≤ n := by
  induction n generalizing t with
  | zero => cases h
  | succ n ih =>
      cases ofMemAppend h with
      | inl hv =>
          obtain ⟨x, hx, heq⟩ := ofMemMap Term.var _ t hv
          cases heq
          exact Nat.succ_le_succ (natsUpTo_sound n x hx)
      | inr hrest =>
          cases ofMemAppend hrest with
          | inl hl =>
              obtain ⟨⟨⟨a, b⟩, body⟩, hp, heq⟩ :=
                ofMemMap (fun ((a, b), body) => Term.lam a b body) _ t hl
              cases heq
              have hp' := ofMemListProd hp
              have hab := ofMemListProd hp'.1
              exact Nat.succ_le_succ (maxLe
                (maxLe (typesUpTo_sound n a hab.1) (typesUpTo_sound n b hab.2))
                (ih body hp'.2))
          | inr hrest =>
              cases ofMemAppend hrest with
              | inl ha =>
                  obtain ⟨⟨f, x⟩, hp, heq⟩ :=
                    ofMemMap (fun (f, x) => Term.app f x) _ t ha
                  cases heq
                  have hp' := ofMemListProd hp
                  exact Nat.succ_le_succ (maxLe (ih f hp'.1) (ih x hp'.2))
              | inr hrest =>
                  cases ofMemAppend hrest with
                  | inl hz =>
                      cases hz with
                      | head => exact Nat.succ_le_succ (Nat.zero_le n)
                      | tail _ ht => cases ht
                  | inr hrest =>
                      cases ofMemAppend hrest with
                      | inl hs =>
                          cases hs with
                          | head => exact Nat.succ_le_succ (Nat.zero_le n)
                          | tail _ ht => cases ht
                      | inr hr =>
                          obtain ⟨r, hm, heq⟩ := ofMemMap Term.natRec _ t hr
                          cases heq
                          exact Nat.succ_le_succ (typesUpTo_sound n r hm)

theorem typesUpTo_correct (n : Nat) (t : Ty) :
    typeDepth t ≤ n ↔ t ∈ typesUpTo n :=
  ⟨typesUpTo_complete n t, typesUpTo_sound n t⟩

theorem natsUpTo_correct (n x : Nat) :
    natDepth x ≤ n ↔ x ∈ natsUpTo n :=
  ⟨natsUpTo_complete n x, natsUpTo_sound n x⟩

theorem termsUpTo_correct (n : Nat) (t : Term) :
    termDepth t ≤ n ↔ t ∈ termsUpTo n :=
  ⟨termsUpTo_complete n t, termsUpTo_sound n t⟩

theorem baseline_mono {m n : Nat} (h : m ≤ n) : baseline m ≤ baseline n := by
  rw [baseline_eq_maximum, baseline_eq_maximum]
  exact maximum_mono eval _ _ (fun t ht =>
    termsUpTo_complete n t (Nat.le_trans (termsUpTo_sound m t ht) h))

end Biggest
