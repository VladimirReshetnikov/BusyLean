import Init

/-!
An executable, constructive Lean port of the computational part of
`codyroux/name-the-biggest-number/Contender.v`.

The source's conventions are preserved: variables use reversed de Bruijn
indices, casts between unequal types return the recursively defined zero
value, casts between arrow types use the two recursively computed directions,
and *all* raw terms (including ill-typed terms) enter the enumeration.

This file defines Contender 5 without evaluating it.  In particular, do not
run `#eval contender5`.
-/

namespace Original

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty
  deriving Repr, DecidableEq

def typeEqb : Ty → Ty → Bool
  | .nat, .nat => true
  | .arr a b, .arr c d => typeEqb a c && typeEqb b d
  | _, _ => false

def typeDepth : Ty → Nat
  | .nat => 1
  | .arr a b => Nat.succ (Nat.max (typeDepth a) (typeDepth b))

def interpType : Ty → Type
  | .nat => Nat
  | .arr a b => interpType a → interpType b

inductive Term where
  | var : Nat → Term
  | lam : Ty → Ty → Term → Term
  | app : Term → Term → Term
  | zero : Term
  | succ : Term
  | natRec : Ty → Term
  deriving Repr, DecidableEq

def natDepth (n : Nat) : Nat := Nat.succ n

def termDepth : Term → Nat
  | .var x => Nat.succ (natDepth x)
  | .lam a b body =>
      Nat.succ (Nat.max (Nat.max (typeDepth a) (typeDepth b)) (termDepth body))
  | .app f x => Nat.succ (Nat.max (termDepth f) (termDepth x))
  | .zero => 1
  | .succ => 1
  | .natRec r => Nat.succ (typeDepth r)

def lookup {α : Type} (env : List α) (n : Nat) : Option α :=
  let len := env.length
  if len ≤ n then none else env[len - Nat.succ n]?

def error : (t : Ty) → interpType t
  | .nat => (0 : Nat)
  | .arr _ b => fun _ => error b

def castError (src dst : Ty) :
    (interpType src → interpType dst) × (interpType dst → interpType src) :=
  (fun _ => error dst, fun _ => error src)

def castImpl : (src dst : Ty) →
    (interpType src → interpType dst) × (interpType dst → interpType src)
  | .nat, .nat => (id, id)
  | .nat, .arr c d => castError .nat (.arr c d)
  | .arr a b, .nat => castError (.arr a b) .nat
  | .arr a b, .arr c d =>
      if typeEqb a c && typeEqb b d then
        let p := castImpl a c
        let q := castImpl b d
        (fun f x => q.1 (f (p.2 x)), fun f x => q.2 (f (p.1 x)))
      else castError (.arr a b) (.arr c d)

def cast {src : Ty} (dst : Ty) : interpType src → interpType dst :=
  (castImpl src dst).1

abbrev Value := (t : Ty) × interpType t

def interpTerm : List Value → Term → Value
  | env, .var x =>
      match lookup env x with
      | some value => value
      | none => ⟨.nat, error .nat⟩
  | env, .lam a b body =>
      ⟨.arr a b, fun x =>
        let value := interpTerm (⟨a, x⟩ :: env) body
        cast b value.2⟩
  | env, .app t₁ t₂ =>
      let value₁ := interpTerm env t₁
      let value₂ := interpTerm env t₂
      match value₁ with
      | ⟨.nat, _⟩ => ⟨.nat, error .nat⟩
      | ⟨.arr a b, f⟩ => ⟨b, f (cast a value₂.2)⟩
  | _, .zero => ⟨.nat, (0 : Nat)⟩
  | _, .succ => ⟨.arr .nat .nat, Nat.succ⟩
  | _, .natRec r =>
      ⟨.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)),
        fun initial step n => Nat.rec initial step n⟩
termination_by structural _ t => t

/- Coq's `list_prod` enumerates the right factor inside the left factor. -/
def listProd {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

def typesUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let r := typesUpTo n
      .nat :: (listProd r r).map (fun (a, b) => .arr a b)

def natsUpTo : Nat → List Nat
  | 0 => []
  | n + 1 => n :: natsUpTo n

def termsUpTo : Nat → List Term
  | 0 => []
  | n + 1 =>
      (natsUpTo n).map Term.var ++ (
      (listProd (listProd (typesUpTo n) (typesUpTo n)) (termsUpTo n)).map
        (fun ((a, b), body) => .lam a b body) ++ (
      (listProd (termsUpTo n) (termsUpTo n)).map (fun (f, x) => .app f x) ++ (
      [.zero] ++ ([.succ] ++ (typesUpTo n).map Term.natRec))))

def eval (t : Term) : Nat :=
  match interpTerm [] t with
  | ⟨.nat, value⟩ => value
  | ⟨.arr _ _, _⟩ => 0

def maxBy {α : Type} (f : α → Nat) : Nat → α → List α → α
  | _, currentBest, [] => currentBest
  | currentMax, currentBest, x :: xs =>
      if currentMax < f x then maxBy f (f x) x xs
      else maxBy f currentMax currentBest xs

def largestOfDepth (n : Nat) : Term := maxBy eval 0 .zero (termsUpTo n)

def largestSTLCNatRecNatOfDepth (n : Nat) : Nat := eval (largestOfDepth n)

/-- The exact computational definition of the repository's Contender 5. -/
def contender5 : Nat := largestSTLCNatRecNatOfDepth 42

/-- A value-only fold, used in proofs; the contender above retains `maxBy`. -/
def foldMax {α : Type} (f : α → Nat) : Nat → List α → Nat
  | currentMax, [] => currentMax
  | currentMax, x :: xs => foldMax f (Nat.max currentMax (f x)) xs

/- These elementary lemmas are reproved to avoid `propext`, which occurs in
some standard-library proofs about `max` despite their constructive content. -/
theorem natMax_eq_left {a b : Nat} (h : b ≤ a) : Nat.max a b = a := by
  change (if a ≤ b then b else a) = a
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    exact Nat.le_antisymm h hab
  · exact if_neg hab

theorem le_natMax_left (a b : Nat) : a ≤ Nat.max a b := by
  change a ≤ if a ≤ b then b else a
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    exact hab
  · rw [if_neg hab]
    exact Nat.le_refl a

theorem le_natMax_right (a b : Nat) : b ≤ Nat.max a b := by
  change b ≤ if a ≤ b then b else a
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    exact Nat.le_refl b
  · rw [if_neg hab]
    exact Nat.le_of_lt (Nat.lt_of_not_ge hab)

theorem maxBy_value {α : Type} (f : α → Nat) (xs : List α)
    (currentMax : Nat) (currentBest : α) (h : f currentBest = currentMax) :
    f (maxBy f currentMax currentBest xs) = foldMax f currentMax xs := by
  induction xs generalizing currentMax currentBest with
  | nil => exact h
  | cons x xs ih =>
      unfold maxBy foldMax
      by_cases hx : currentMax < f x
      · rw [if_pos hx, Nat.max_eq_max, Nat.max_eq_right (Nat.le_of_lt hx)]
        exact ih (f x) x rfl
      · rw [if_neg hx, natMax_eq_left (Nat.le_of_not_gt hx)]
        exact ih currentMax currentBest h

theorem largestSTLCNatRecNatOfDepth_eq_foldMax (n : Nat) :
    largestSTLCNatRecNatOfDepth n = foldMax eval 0 (termsUpTo n) :=
  maxBy_value eval (termsUpTo n) 0 .zero rfl

theorem current_le_foldMax {α : Type} (f : α → Nat) (xs : List α)
    (currentMax : Nat) : currentMax ≤ foldMax f currentMax xs := by
  induction xs generalizing currentMax with
  | nil => exact Nat.le_refl currentMax
  | cons x xs ih =>
      exact Nat.le_trans (le_natMax_left currentMax (f x))
        (ih (Nat.max currentMax (f x)))

theorem le_foldMax_of_mem {α : Type} (f : α → Nat) (xs : List α)
    (x : α) (h : x ∈ xs) (currentMax : Nat) :
    f x ≤ foldMax f currentMax xs := by
  induction xs generalizing currentMax with
  | nil => cases h
  | cons y ys ih =>
      cases h with
      | head =>
          exact Nat.le_trans (le_natMax_right currentMax (f x))
            (current_le_foldMax f ys (Nat.max currentMax (f x)))
      | tail _ h => exact ih h (Nat.max currentMax (f y))

theorem eval_le_largest_of_mem (n : Nat) (t : Term) (h : t ∈ termsUpTo n) :
    eval t ≤ largestSTLCNatRecNatOfDepth n := by
  rw [largestSTLCNatRecNatOfDepth_eq_foldMax]
  exact le_foldMax_of_mem eval (termsUpTo n) t h 0

/- Direct membership lemmas keep all subsequent coverage proofs axiom-free. -/
theorem map_mem {α β : Type} (f : α → β) {x : α} {xs : List α}
    (h : x ∈ xs) : f x ∈ xs.map f := by
  induction h with
  | head => exact .head _
  | tail y _ ih => exact .tail (f y) ih

theorem of_map_mem {α β : Type} (f : α → β) {y : β} {xs : List α}
    (h : y ∈ xs.map f) : ∃ x, x ∈ xs ∧ f x = y := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
      cases h with
      | head => exact ⟨x, .head _, rfl⟩
      | tail _ h =>
          obtain ⟨z, hz, he⟩ := ih h
          exact ⟨z, .tail x hz, he⟩

theorem of_append_mem {α : Type} {x : α} (xs ys : List α)
    (h : x ∈ xs ++ ys) : x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => exact Or.inr h
  | cons y xs ih =>
      cases h with
      | head => exact Or.inl (.head _)
      | tail _ h =>
          cases ih h with
          | inl hx => exact Or.inl (.tail y hx)
          | inr hx => exact Or.inr hx

theorem flatMap_mem {α β : Type} (f : α → List β) {x : α} {xs : List α}
    {y : β} (hx : x ∈ xs) (hy : y ∈ f x) : y ∈ xs.flatMap f := by
  induction hx with
  | head => exact List.mem_append_left _ hy
  | tail z _ ih => exact List.mem_append_right (f z) ih

theorem of_flatMap_mem {α β : Type} (f : α → List β) {xs : List α} {y : β}
    (h : y ∈ xs.flatMap f) : ∃ x, x ∈ xs ∧ y ∈ f x := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
      cases of_append_mem (f x) (xs.flatMap f) h with
      | inl hy => exact ⟨x, .head _, hy⟩
      | inr hy =>
          obtain ⟨z, hz, he⟩ := ih hy
          exact ⟨z, .tail x hz, he⟩

theorem listProd_mem {α β : Type} {x : α} {y : β} {xs : List α} {ys : List β}
    (hx : x ∈ xs) (hy : y ∈ ys) : (x, y) ∈ listProd xs ys :=
  flatMap_mem (fun a => ys.map (fun b => (a, b))) hx
    (map_mem (fun b => (x, b)) hy)

theorem of_listProd_mem {α β : Type} {x : α} {y : β} {xs : List α} {ys : List β}
    (h : (x, y) ∈ listProd xs ys) : x ∈ xs ∧ y ∈ ys := by
  obtain ⟨a, ha, hab⟩ := of_flatMap_mem (fun a => ys.map (fun b => (a, b))) h
  obtain ⟨b, hb, he⟩ := of_map_mem (fun b => (a, b)) hab
  cases he
  exact ⟨ha, hb⟩

theorem typeDepth_pos (t : Ty) : 1 ≤ typeDepth t := by
  cases t with
  | nat => exact Nat.le_refl 1
  | arr a b => exact Nat.succ_le_succ (Nat.zero_le _)

theorem termDepth_pos (t : Term) : 1 ≤ termDepth t := by
  cases t <;> exact Nat.succ_le_succ (Nat.zero_le _)

theorem typesUpTo_complete (n : Nat) (t : Ty) (h : typeDepth t ≤ n) :
    t ∈ typesUpTo n := by
  induction n generalizing t with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (typeDepth_pos t) h))
  | succ n ih =>
      cases t with
      | nat => exact .head _
      | arr a b =>
          have hm := Nat.le_of_succ_le_succ h
          exact .tail _ (map_mem (fun (x, y) => Ty.arr x y)
            (listProd_mem
              (ih a (Nat.le_trans (le_natMax_left _ _) hm))
              (ih b (Nat.le_trans (le_natMax_right _ _) hm))))

theorem natsUpTo_complete (n m : Nat) (h : natDepth m ≤ n) : m ∈ natsUpTo n := by
  induction n with
  | zero => exact False.elim (Nat.not_succ_le_zero m h)
  | succ n ih =>
      have hmn := Nat.le_of_succ_le_succ h
      cases Nat.eq_or_lt_of_le hmn with
      | inl he => cases he; exact .head _
      | inr hl => exact .tail n (ih hl)

theorem termsUpTo_complete (n : Nat) (t : Term) (h : termDepth t ≤ n) :
    t ∈ termsUpTo n := by
  induction n generalizing t with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (termDepth_pos t) h))
  | succ n ih =>
      cases t with
      | var x =>
          exact List.mem_append_left _
            (map_mem Term.var (natsUpTo_complete n x (Nat.le_of_succ_le_succ h)))
      | lam a b body =>
          have hm := Nat.le_of_succ_le_succ h
          have hab := Nat.le_trans (le_natMax_left _ _) hm
          have hb := Nat.le_trans (le_natMax_right _ _) hm
          exact List.mem_append_right _ (List.mem_append_left _
            (map_mem (fun ((a, b), body) => Term.lam a b body)
              (listProd_mem
                (listProd_mem
                  (typesUpTo_complete n a (Nat.le_trans (le_natMax_left _ _) hab))
                  (typesUpTo_complete n b (Nat.le_trans (le_natMax_right _ _) hab)))
                (ih body hb))))
      | app f x =>
          have hm := Nat.le_of_succ_le_succ h
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_left _
              (map_mem (fun (f, x) => Term.app f x)
                (listProd_mem
                  (ih f (Nat.le_trans (le_natMax_left _ _) hm))
                  (ih x (Nat.le_trans (le_natMax_right _ _) hm))))))
      | zero =>
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (.head _)))
      | succ =>
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (.tail _ (.head _))))
      | natRec r =>
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (.tail _ (.tail _
              (map_mem Term.natRec
                (typesUpTo_complete n r (Nat.le_of_succ_le_succ h)))))))

theorem natMax_le {a b n : Nat} (ha : a ≤ n) (hb : b ≤ n) : Nat.max a b ≤ n := by
  change (if a ≤ b then b else a) ≤ n
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact hb
  · rw [if_neg h]
    exact ha

theorem typesUpTo_sound (n : Nat) (t : Ty) (h : t ∈ typesUpTo n) :
    typeDepth t ≤ n := by
  induction n generalizing t with
  | zero => cases h
  | succ n ih =>
      cases h with
      | head => exact Nat.succ_le_succ (Nat.zero_le n)
      | tail _ h =>
          obtain ⟨⟨a, b⟩, hab, he⟩ := of_map_mem (fun (a, b) => Ty.arr a b) h
          cases he
          obtain ⟨ha, hb⟩ := of_listProd_mem hab
          exact Nat.succ_le_succ (natMax_le (ih a ha) (ih b hb))

theorem natsUpTo_sound (n m : Nat) (h : m ∈ natsUpTo n) : natDepth m ≤ n := by
  induction n with
  | zero => cases h
  | succ n ih =>
      cases h with
      | head => exact Nat.le_refl _
      | tail _ h => exact Nat.le_step (ih h)

theorem termsUpTo_sound (n : Nat) (t : Term) (h : t ∈ termsUpTo n) :
    termDepth t ≤ n := by
  induction n generalizing t with
  | zero => cases h
  | succ n ih =>
      cases of_append_mem _ _ h with
      | inl h =>
          obtain ⟨x, hx, he⟩ := of_map_mem Term.var h
          cases he
          exact Nat.succ_le_succ (natsUpTo_sound n x hx)
      | inr h =>
          cases of_append_mem _ _ h with
          | inl h =>
              obtain ⟨⟨⟨a, b⟩, body⟩, hab, he⟩ :=
                of_map_mem (fun ((a, b), body) => Term.lam a b body) h
              cases he
              obtain ⟨ht, hb⟩ := of_listProd_mem hab
              obtain ⟨ha, hb'⟩ := of_listProd_mem ht
              exact Nat.succ_le_succ (natMax_le
                (natMax_le (typesUpTo_sound n a ha) (typesUpTo_sound n b hb'))
                (ih body hb))
          | inr h =>
              cases of_append_mem _ _ h with
              | inl h =>
                  obtain ⟨⟨f, x⟩, hfx, he⟩ := of_map_mem (fun (f, x) => Term.app f x) h
                  cases he
                  obtain ⟨hf, hx⟩ := of_listProd_mem hfx
                  exact Nat.succ_le_succ (natMax_le (ih f hf) (ih x hx))
              | inr h =>
                  cases h with
                  | head => exact Nat.succ_le_succ (Nat.zero_le n)
                  | tail _ h =>
                      cases h with
                      | head => exact Nat.succ_le_succ (Nat.zero_le n)
                      | tail _ h =>
                          obtain ⟨r, hr, he⟩ := of_map_mem Term.natRec h
                          cases he
                          exact Nat.succ_le_succ (typesUpTo_sound n r hr)

theorem typesUpTo_correct (n : Nat) (t : Ty) :
    typeDepth t ≤ n ↔ t ∈ typesUpTo n :=
  ⟨typesUpTo_complete n t, typesUpTo_sound n t⟩

theorem termsUpTo_correct (n : Nat) (t : Term) :
    termDepth t ≤ n ↔ t ∈ termsUpTo n :=
  ⟨termsUpTo_complete n t, termsUpTo_sound n t⟩

theorem termsUpTo_mono {m n : Nat} (h : m ≤ n) {t : Term}
    (ht : t ∈ termsUpTo m) : t ∈ termsUpTo n :=
  termsUpTo_complete n t (Nat.le_trans (termsUpTo_sound m t ht) h)

end Original
