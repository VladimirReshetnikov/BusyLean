import BusyLean.Ordinal.SortedLex
import BusyLean.SystemFL.Transfinite

/-!
# Atoms below `ε₀`

A tree `node [a₁, …, a_k]` denotes `ω^a₁ + ⋯ + ω^a_k`. It is in normal form when
its children are in normal form and non-increasing. Trees are compared
lexicographically, child by child. On normal forms this is the ordinal order
below `ε₀`.

Well-foundedness reuses `SortedLex` hereditarily. On arbitrary trees the
lexicographic order has infinite descending chains, so normality is built into
the Boolean element order: `ltP a b := nf a && lt a b`. The accessible part then
contains every normal form: the head child is accessible by recursion, the list
of children is accessible by `acc_head`, and the tree inherits it, because a
smaller normal tree has a smaller list of children.
-/

namespace BusyLean.Ordinal

/-- Cantor normal form trees: `node [a₁, …, a_k] = ω^a₁ + ⋯ + ω^a_k`. -/
inductive Cnf where
  | node : List Cnf → Cnf

namespace Cnf

mutual
def decEq : (a b : Cnf) → Decidable (a = b)
  | node xs, node ys =>
      match decEqList xs ys with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (Cnf.node.inj e)

def decEqList : (xs ys : List Cnf) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun e => nomatch e
  | _ :: _, [] => isFalse fun e => nomatch e
  | x :: xs, y :: ys =>
      match decEq x y, decEqList xs ys with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun e => h₁ (List.cons.inj e).1
      | _, isFalse h₂ => isFalse fun e => h₂ (List.cons.inj e).2
end

instance : DecidableEq Cnf := decEq

mutual
/-- The lexicographic order on trees. -/
def lt : Cnf → Cnf → Bool
  | node xs, node ys => llt' xs ys

def llt' : List Cnf → List Cnf → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => lt x y || (decide (x = y) && llt' xs ys)
end

mutual
/-- Normal forms: children in normal form and non-increasing. -/
def nf : Cnf → Bool
  | node xs => sorted lt xs && nfAll xs

def nfAll : List Cnf → Bool
  | [] => true
  | x :: xs => nf x && nfAll xs
end

theorem llt'_eq : ∀ xs ys : List Cnf, llt' xs ys = Ordinal.llt lt xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      simp only [llt', Ordinal.llt, llt'_eq xs ys]

/-- The order with normality built in. -/
def ltP (a b : Cnf) : Bool := nf a && lt a b

theorem llt_ltP : ∀ ys xs : List Cnf, nfAll ys = true →
    Ordinal.llt ltP ys xs = Ordinal.llt lt ys xs
  | [], [] , _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | y :: ys, x :: xs, h => by
      simp only [nfAll, Bool.and_eq_true] at h
      simp only [Ordinal.llt, ltP, h.1, Bool.true_and, llt_ltP ys xs h.2]

theorem sorted_ltP : ∀ xs : List Cnf, nfAll xs = true → sorted lt xs = true → sorted ltP xs = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: t, ha, hs => by
      simp only [nfAll, Bool.and_eq_true] at ha
      have hst := sorted_tail hs
      simp only [sorted, Bool.and_eq_true] at hs ⊢
      refine ⟨?_, sorted_ltP (y :: t) (by simp only [nfAll, Bool.and_eq_true]; exact ha.2) hst⟩
      have h1 := hs.1
      simp only [Ordinal.le, Bool.or_eq_true] at h1 ⊢
      rcases h1 with h1 | h1
      · exact Or.inl (by simp only [ltP, ha.2.1, h1, Bool.and_self])
      · exact Or.inr h1

/-- A tree whose list of children is accessible is accessible. -/
theorem acc_of_children : ∀ l : List Cnf, Acc (SR ltP) l → Acc (LT' ltP) (node l) := by
  intro l hl
  induction hl with
  | intro l _ ih =>
    refine Acc.intro _ fun t' ht' => ?_
    match t', ht' with
    | node ys, ht' =>
      simp only [LT', ltP, nf, Bool.and_eq_true] at ht'
      obtain ⟨⟨hs, ha⟩, hlt⟩ := ht'
      refine ih ys ⟨sorted_ltP ys ha hs, ?_⟩
      rw [llt_ltP ys l ha, ← llt'_eq]
      exact hlt

/-- **Every normal form is accessible.** -/
theorem acc_nf : ∀ t : Cnf, nf t = true → Acc (LT' ltP) t
  | node [], _ => acc_of_children [] acc_nil
  | node (x :: xs), h => by
      simp only [nf, Bool.and_eq_true] at h
      have hx : nf x = true := by
        have := h.2
        simp only [nfAll, Bool.and_eq_true] at this
        exact this.1
      exact acc_of_children _
        (acc_head (acc_nf x hx) (x :: xs) (sorted_ltP _ h.2 h.1) rfl)

end Cnf

/-- Notations for the ordinals below `ε₀`. -/
def Epsilon0 : Type := {t : Cnf // Cnf.nf t = true}

instance : DecidableEq Epsilon0 := fun a b =>
  if h : a.1 = b.1 then isTrue (Subtype.ext h) else isFalse (fun e => h (congrArg Subtype.val e))

instance : FL.AtomOrder Epsilon0 := ⟨fun a b => Cnf.lt a.1 b.1⟩

theorem epsilon0_wf : WellFounded (FL.ALt (α := Epsilon0)) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨t, ht⟩ := a
  have h := Cnf.acc_nf t ht
  induction h with
  | intro t _ ih =>
    exact Acc.intro _ fun b hb => by
      obtain ⟨t', ht'⟩ := b
      refine ih t' ?_ ht'
      show Cnf.ltP t' t = true
      simp only [Cnf.ltP, ht', Bool.true_and]
      exact hb

/-- Lists of length `≤ L` over `es`. -/
def listsOf {γ : Type} (es : List γ) : Nat → List (List γ)
  | 0 => [[]]
  | L + 1 => [] :: es.flatMap fun e => (listsOf es L).map (e :: ·)

/-- Trees of height `≤ n` with at most `n` children per node. -/
def cnfsUpTo : Nat → List Cnf
  | 0 => []
  | n + 1 => (listsOf (cnfsUpTo n) n).map Cnf.node

/-- Atoms of enumeration depth `n`: the normal forms among `cnfsUpTo n`. -/
def epsilon0UpTo (n : Nat) : List Epsilon0 :=
  (cnfsUpTo n).filterMap fun t => if h : Cnf.nf t = true then some ⟨t, h⟩ else none

end BusyLean.Ordinal
