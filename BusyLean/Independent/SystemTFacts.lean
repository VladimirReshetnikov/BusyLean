import BusyLean.Contender5

/-!
# Facts about Contender 5's language (System T)

Shared by the independent tower's comparisons: interpretation of applications
and casts, enumeration of terms by depth, and the `maxBy` winner selection.
-/

namespace BusyLean.Indep

open BusyLean.C5

/-! ## Interpreting applications and casts -/

theorem typeEqb_refl : ∀ a : Ty, typeEqb a a = true
  | .nat => rfl
  | .arr a b => by simp [typeEqb, typeEqb_refl a, typeEqb_refl b]

theorem castImpl_same : ∀ a : Ty, (∀ x : den a, (castImpl a a).1 x = x) ∧
    (∀ x : den a, (castImpl a a).2 x = x)
  | .nat => ⟨fun _ => rfl, fun _ => rfl⟩
  | .arr a b => by
      have h : (typeEqb a a && typeEqb b b) = true := by simp [typeEqb_refl]
      have ha := castImpl_same a
      have hb := castImpl_same b
      refine ⟨fun f => ?_, fun f => ?_⟩
      · show (match typeEqb a a && typeEqb b b with
          | true => _
          | false => castError (.arr a b) (.arr a b)).1 f = f
        rw [h]
        funext x
        simp only [ha.2, hb.1]
      · show (match typeEqb a a && typeEqb b b with
          | true => _
          | false => castError (.arr a b) (.arr a b)).2 f = f
        rw [h]
        funext x
        simp only [ha.1, hb.2]

theorem cast_same {a : Ty} (x : den a) : cast a x = x := (castImpl_same a).1 x

abbrev N2' : Ty := .arr .nat .nat

theorem interp_app {e : List Value} {t u : Term} {a b : Ty} {f : den a → den b} {x : den a}
    (ht : interp e t = (⟨.arr a b, f⟩ : Value)) (hu : interp e u = (⟨a, x⟩ : Value)) :
    interp e (.app t u) = (⟨b, f x⟩ : Value) := by
  simp only [interp, ht, hu, cast_same]

theorem interp_succ (e : List Value) : interp e .succ = (⟨N2', Nat.succ⟩ : Value) := rfl

theorem eval_of_interp {t : Term} {n : Nat} (h : interp [] t = (⟨.nat, n⟩ : Value)) :
    eval t = n := by
  unfold eval; rw [h]

/-! ## Enumeration by depth -/

def tyDepth : Ty → Nat
  | .nat => 1
  | .arr a b => max (tyDepth a) (tyDepth b) + 1

def depth : Term → Nat
  | .var x => x + 2
  | .lam a b t => max (max (tyDepth a) (tyDepth b)) (depth t) + 1
  | .app t u => max (depth t) (depth u) + 1
  | .zero => 1
  | .succ => 1
  | .natRec r => tyDepth r + 1

theorem mem_listProd {α β : Type} {x : α} {y : β} :
    ∀ {xs : List α} {ys : List β}, x ∈ xs → y ∈ ys → (x, y) ∈ listProd xs ys
  | _ :: _, _, .head _, hy => List.mem_append_left _ (List.mem_map_of_mem hy)
  | _ :: _, _, .tail _ hx, hy => List.mem_append_right _ (mem_listProd hx hy)

theorem mem_natsUpTo : ∀ {m x : Nat}, x < m → x ∈ natsUpTo m
  | m + 1, x, h => by
      by_cases e : x = m
      · subst e; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_natsUpTo (by omega))

theorem le_of_max_left {a b c : Nat} (h : max a b ≤ c) : a ≤ c :=
  Nat.le_trans (Nat.le_max_left a b) h

theorem le_of_max_right {a b c : Nat} (h : max a b ≤ c) : b ≤ c :=
  Nat.le_trans (Nat.le_max_right a b) h

theorem mem_typesUpTo : ∀ (a : Ty) {m : Nat}, tyDepth a ≤ m → a ∈ typesUpTo m
  | .nat, m + 1, _ => List.mem_cons_self
  | .arr a b, m + 1, h => by
      have h' := Nat.le_of_succ_le_succ h
      refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, b), ?_, rfl⟩)
      exact mem_listProd (mem_typesUpTo a (le_of_max_left h')) (mem_typesUpTo b (le_of_max_right h'))
  | .nat, 0, h => absurd h (by decide)
  | .arr _ _, 0, h => absurd h (Nat.not_succ_le_zero _)

theorem mem_termsUpTo : ∀ (t : Term) {m : Nat}, depth t ≤ m → t ∈ termsUpTo m
  | .var _, 0, h | .lam _ _ _, 0, h | .app _ _, 0, h | .natRec _, 0, h =>
      absurd h (Nat.not_succ_le_zero _)
  | .zero, 0, h | .succ, 0, h => absurd h (by decide)
  | .var x, m + 1, h =>
      List.mem_append_left _ (List.mem_map_of_mem (mem_natsUpTo (Nat.lt_of_succ_lt_succ h)))
  | .lam a b t, m + 1, h => by
      have h' := Nat.le_of_succ_le_succ h
      refine List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨((a, b), t), ?_, rfl⟩))
      exact mem_listProd (mem_listProd (mem_typesUpTo a (le_of_max_left (le_of_max_left h')))
          (mem_typesUpTo b (le_of_max_right (le_of_max_left h'))))
        (mem_termsUpTo t (le_of_max_right h'))
  | .app t u, m + 1, h => by
      have h' := Nat.le_of_succ_le_succ h
      refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨(t, u), ?_, rfl⟩)))
      exact mem_listProd (mem_termsUpTo t (le_of_max_left h')) (mem_termsUpTo u (le_of_max_right h'))
  | .zero, m + 1, _ =>
      List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ List.mem_cons_self)))
  | .succ, m + 1, _ =>
      List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self))))
  | .natRec r, m + 1, h =>
      List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _
          (List.mem_map_of_mem (mem_typesUpTo r (Nat.le_of_succ_le_succ h)))))))

/-! ## `maxBy` attains every listed value -/

theorem maxBy_ge_current {α : Type} (f : α → Nat) :
    ∀ (l : List α) (cm : Nat) (cb : α), f cb = cm → cm ≤ f (maxBy f cm cb l)
  | [], _, _, h => Nat.le_of_eq h.symm
  | x :: l, cm, cb, h => by
      simp only [maxBy]
      cases hb : Nat.blt cm (f x) with
      | true =>
          have := Nat.le_of_lt (Nat.blt_eq.mp hb)
          exact Nat.le_trans this (maxBy_ge_current f l (f x) x rfl)
      | false => exact maxBy_ge_current f l cm cb h

theorem le_maxBy {α : Type} (f : α → Nat) {x : α} :
    ∀ {l : List α} (cm : Nat) (cb : α), x ∈ l → f cb = cm → f x ≤ f (maxBy f cm cb l)
  | y :: l, cm, cb, hx, h => by
      simp only [maxBy]
      cases hx with
      | head =>
          cases hb : Nat.blt cm (f x) with
          | true => exact maxBy_ge_current f l (f x) x rfl
          | false =>
              have : f x ≤ cm := Nat.not_lt.mp fun h' => by
                rw [Nat.blt_eq.mpr h'] at hb; cases hb
              exact Nat.le_trans this (maxBy_ge_current f l cm cb h)
      | tail _ hx =>
          cases hb : Nat.blt cm (f y) with
          | true => exact le_maxBy f (f y) y hx rfl
          | false => exact le_maxBy f cm cb hx h

theorem eval_le_largest {t : Term} {m : Nat} (h : depth t ≤ m) :
    eval t ≤ largestSTLCNatRecNatOfDepth m :=
  le_maxBy eval 0 .zero (mem_termsUpTo t h) rfl


/-! ## Numerals -/

abbrev N : Ty := .nat
abbrev N2 : Ty := .arr .nat .nat
abbrev N3 : Ty := .arr .nat N2

/-- The numeral `succⁿ zero`. -/
def numT : Nat → Term
  | 0 => .zero
  | n + 1 => .app .succ (numT n)

theorem interp_numT (e : List Value) : ∀ n, interp e (numT n) = ⟨.nat, n⟩
  | 0 => rfl
  | n + 1 => interp_app (interp_succ _) (interp_numT e n)

/-! ## Converse facts: the winner is listed, listed terms are shallow -/

theorem maxBy_mem {α : Type} (f : α → Nat) :
    ∀ (l : List α) (cm : Nat) (cb : α), maxBy f cm cb l ∈ l ∨ maxBy f cm cb l = cb
  | [], _, _ => Or.inr rfl
  | x :: l, cm, cb => by
      simp only [maxBy]
      cases Nat.blt cm (f x) with
      | true =>
          rcases maxBy_mem f l (f x) x with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · rw [h]; exact Or.inl List.mem_cons_self
      | false =>
          rcases maxBy_mem f l cm cb with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h

theorem mem_of_mem_listProd {α β : Type} {x : α} {y : β} :
    ∀ {xs : List α} {ys : List β}, (x, y) ∈ listProd xs ys → x ∈ xs ∧ y ∈ ys
  | [], _, h => nomatch h
  | z :: zs, ys, h => by
      rcases List.mem_append.mp h with h | h
      · obtain ⟨y', hy', e⟩ := List.mem_map.mp h
        cases e
        exact ⟨List.mem_cons_self, hy'⟩
      · obtain ⟨hx, hy⟩ := mem_of_mem_listProd h
        exact ⟨List.mem_cons_of_mem _ hx, hy⟩

theorem lt_of_mem_natsUpTo : ∀ {m x : Nat}, x ∈ natsUpTo m → x < m
  | 0, _, h => nomatch h
  | m + 1, x, h => by
      rcases List.mem_cons.mp h with h | h
      · rw [h]; exact Nat.lt_succ_self m
      · exact Nat.lt_succ_of_lt (lt_of_mem_natsUpTo h)

theorem tyDepth_of_mem : ∀ {m : Nat} {a : Ty}, a ∈ typesUpTo m → tyDepth a ≤ m
  | 0, _, h => nomatch h
  | m + 1, a, h => by
      rcases List.mem_cons.mp h with h | h
      · rw [h]; exact Nat.succ_le_succ (Nat.zero_le m)
      · obtain ⟨⟨b, c⟩, hp, e⟩ := List.mem_map.mp h
        cases e
        obtain ⟨hb, hc⟩ := mem_of_mem_listProd hp
        exact Nat.succ_le_succ (Nat.max_le.mpr ⟨tyDepth_of_mem hb, tyDepth_of_mem hc⟩)

theorem depth_of_mem : ∀ {m : Nat} {t : Term}, t ∈ termsUpTo m → depth t ≤ m
  | 0, _, h => nomatch h
  | m + 1, t, h => by
      simp only [termsUpTo, List.mem_append, List.mem_map, List.mem_cons] at h
      rcases h with ⟨x, hx, e⟩ | ⟨⟨⟨a, b⟩, u⟩, hp, e⟩ | ⟨⟨u, v⟩, hp, e⟩ | e | e | ⟨r, hr, e⟩
      · subst e
        exact Nat.succ_le_succ (lt_of_mem_natsUpTo hx)
      · subst e
        obtain ⟨hab, hu⟩ := mem_of_mem_listProd hp
        obtain ⟨ha, hb⟩ := mem_of_mem_listProd hab
        exact Nat.succ_le_succ (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨tyDepth_of_mem ha,
          tyDepth_of_mem hb⟩, depth_of_mem hu⟩)
      · subst e
        obtain ⟨hu, hv⟩ := mem_of_mem_listProd hp
        exact Nat.succ_le_succ (Nat.max_le.mpr ⟨depth_of_mem hu, depth_of_mem hv⟩)
      · rcases e with e | e
        · subst e; exact Nat.succ_le_succ (Nat.zero_le m)
        · exact nomatch e
      · rcases e with e | e
        · subst e; exact Nat.succ_le_succ (Nat.zero_le m)
        · exact nomatch e
      · subst e; exact Nat.succ_le_succ (tyDepth_of_mem hr)

end BusyLean.Indep
