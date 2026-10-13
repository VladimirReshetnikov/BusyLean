import BusyLean.Ordinal.Epsilon0

/-!
# Atoms below `Γ₀`: binary Veblen normal forms

Terms are sums of principal terms `φ(a, b)`: `node [φ(a₁,b₁), …, φ(a_k,b_k)]`.
Sums are compared lexicographically, and principal terms by Veblen's rule:

* `φ(a,b) < φ(c,d)` if `a < c` and `b < φ(c,d)`;
* `φ(a,b) < φ(c,d)` if `a = c` and `b < d`;
* otherwise, `φ(a,b) < φ(c,d)` if `φ(a,b) ≤ d`.

A term is *normal* when every sum is non-increasing (hereditarily). The
genuine Veblen normal forms are among them, so the order type is at least `Γ₀`.

The well-foundedness proof follows Schütte's argument but uses only the
**definitional case split** of the Boolean comparison. It needs no
transitivity, trichotomy or ordinal arithmetic. `acc_phi` shows by induction
on `a`, then `b`, then the size of the predecessor, that `φ(a,b)` is accessible
whenever `a` and `b` are. Sums are handled by `SortedLex`, exactly as for `ε₀`.
-/

namespace BusyLean.Ordinal

namespace Veblen

mutual
/-- Sums `node [p₁, …, p_k]` of principal terms. -/
inductive V where
  | node : List P → V
/-- Principal terms `φ(a, b)`. -/
inductive P where
  | phi : V → V → P
end

mutual
def decEqV : (x y : V) → Decidable (x = y)
  | .node l, .node m =>
      match decEqL l m with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (V.node.inj e)

def decEqP : (p q : P) → Decidable (p = q)
  | .phi a b, .phi c d =>
      match decEqV a c, decEqV b d with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun e => h₁ (P.phi.inj e).1
      | _, isFalse h₂ => isFalse fun e => h₂ (P.phi.inj e).2

def decEqL : (l m : List P) → Decidable (l = m)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun e => nomatch e
  | _ :: _, [] => isFalse fun e => nomatch e
  | p :: l, q :: m =>
      match decEqP p q, decEqL l m with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun e => h₁ (List.cons.inj e).1
      | _, isFalse h₂ => isFalse fun e => h₂ (List.cons.inj e).2
end

instance : DecidableEq V := decEqV
instance : DecidableEq P := decEqP

mutual
def V.size : V → Nat
  | .node l => 1 + sizeL l
def sizeL : List P → Nat
  | [] => 0
  | p :: l => 1 + p.size + sizeL l
def P.size : P → Nat
  | .phi a b => 1 + a.size + b.size
end

theorem V.size_pos (x : V) : 0 < x.size := by
  cases x; simp only [V.size]; omega

mutual
/-- The order on sums. -/
def ltV : V → V → Bool
  | .node l, .node m => ltL l m
termination_by x y => x.size + y.size
decreasing_by all_goals simp only [V.size]; omega

def ltL : List P → List P → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | p :: l, q :: m => ltP p q || (decide (p = q) && ltL l m)
termination_by l m => sizeL l + sizeL m
decreasing_by all_goals simp only [sizeL]; omega

/-- Veblen's rule for principal terms. -/
def ltP : P → P → Bool
  | .phi a b, .phi c d =>
      if ltV a c then ltVP b c d
      else if decide (a = c) then ltV b d
      else leVP a b d
termination_by p q => p.size + q.size
decreasing_by
  all_goals simp only [P.size]
  all_goals have := V.size_pos a; have := V.size_pos c
  all_goals omega

/-- `b < φ(c, d)`. -/
def ltVP : V → V → V → Bool
  | .node [], _, _ => true
  | .node (p :: _), c, d => ltP p (.phi c d)
termination_by b c d => b.size + c.size + d.size + 1
decreasing_by all_goals simp only [V.size, sizeL, P.size]; omega

/-- `φ(a, b) ≤ d`. -/
def leVP : V → V → V → Bool
  | _, _, .node [] => false
  | a, b, .node (q :: _) => ltP (.phi a b) q || decide (P.phi a b = q)
termination_by a b d => a.size + b.size + d.size + 1
decreasing_by all_goals simp only [V.size, sizeL, P.size]; omega
end

mutual
/-- Normal terms: every sum non-increasing, hereditarily. -/
def nfV : V → Bool
  | .node l => sorted ltP l && nfL l
def nfL : List P → Bool
  | [] => true
  | p :: l => nfP p && nfL l
def nfP : P → Bool
  | .phi a b => nfV a && nfV b
end

/-- Orders with normality built in. -/
def ltPN (p q : P) : Bool := nfP p && ltP p q
def ltVN (x y : V) : Bool := nfV x && ltV x y

abbrev AccV := Acc (LT' ltVN)
abbrev AccP := Acc (LT' ltPN)

theorem ltL_eq : ∀ l m : List P, ltL l m = Ordinal.llt ltP l m
  | [], [] => by rw [ltL]; rfl
  | [], _ :: _ => by rw [ltL]; rfl
  | _ :: _, [] => by rw [ltL]; rfl
  | p :: l, q :: m => by rw [ltL, ltL_eq l m]; rfl

theorem llt_ltPN : ∀ l m : List P, nfL l = true → Ordinal.llt ltPN l m = Ordinal.llt ltP l m
  | [], [] , _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: l, q :: m, h => by
      simp only [nfL, Bool.and_eq_true] at h
      simp only [Ordinal.llt, ltPN, h.1, Bool.true_and, llt_ltPN l m h.2]

theorem sorted_ltPN : ∀ l : List P, nfL l = true → sorted ltP l = true → sorted ltPN l = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: t, ha, hs => by
      simp only [nfL, Bool.and_eq_true] at ha
      have hst := sorted_tail hs
      simp only [sorted, Bool.and_eq_true] at hs ⊢
      refine ⟨?_, sorted_ltPN (y :: t) (by simp only [nfL, Bool.and_eq_true]; exact ha.2) hst⟩
      have h1 := hs.1
      simp only [Ordinal.le, Bool.or_eq_true] at h1 ⊢
      rcases h1 with h1 | h1
      · exact Or.inl (by simp only [ltPN, ha.2.1, h1, Bool.and_self])
      · exact Or.inr h1

theorem ltV_node (l m : List P) : ltV (.node l) (.node m) = ltL l m := by rw [ltV]

/-- A sum whose list of summands is accessible is accessible. -/
theorem acc_of_children : ∀ l : List P, Acc (SR ltPN) l → AccV (.node l) := by
  intro l hl
  induction hl with
  | intro l _ ih =>
    refine Acc.intro _ fun x hx => ?_
    match x, hx with
    | .node m, hx =>
      simp only [LT', ltVN, nfV, Bool.and_eq_true] at hx
      obtain ⟨⟨hs, ha⟩, hlt⟩ := hx
      refine ih m ⟨sorted_ltPN m ha hs, ?_⟩
      rw [llt_ltPN m l ha, ← ltL_eq, ← ltV_node]
      exact hlt

theorem accV_zero : AccV (.node []) :=
  Acc.intro _ fun x hx => by
    match x, hx with
    | .node m, hx =>
      simp only [LT', ltVN, ltV_node, Bool.and_eq_true] at hx
      have := hx.2
      rw [ltL_eq, llt_nil_right] at this
      cases this

/-- A normal sum headed by an accessible principal term is accessible. -/
theorem accV_of_head {p : P} {l : List P} (hp : AccP p) (hn : nfV (.node (p :: l)) = true) :
    AccV (.node (p :: l)) := by
  simp only [nfV, Bool.and_eq_true] at hn
  exact acc_of_children _ (acc_head hp (p :: l) (sorted_ltPN _ hn.2 hn.1) rfl)

/-- A principal term is accessible when the one-term sum is. -/
theorem accP_of_single {p : P} (h : AccV (.node [p])) : AccP p := by
  generalize hx : V.node [p] = x at h
  induction h generalizing p with
  | intro x _ ih =>
    subst hx
    refine Acc.intro _ fun q hq => ?_
    simp only [LT', ltPN, Bool.and_eq_true] at hq
    refine ih (.node [q]) ?_ rfl
    show ltVN (.node [q]) (.node [p]) = true
    simp only [ltVN, nfV, nfL, hq.1, ltV_node, ltL_eq, Ordinal.llt, hq.2, Bool.true_or,
      Bool.and_true]
    rfl

/-- Accessible sums bound their principal terms: if `φ(e,f) ≤ b` then `φ(e,f)` is accessible. -/
theorem accP_of_le {e f b : V} (hb : AccV b) (hq : nfP (.phi e f) = true)
    (hle : leVP e f b = true) : AccP (.phi e f) := by
  match b, hb, hle with
  | .node [], _, hle => rw [leVP] at hle; cases hle
  | .node (r :: m), hb, hle =>
    rw [leVP] at hle
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hle
    apply accP_of_single
    have hn : nfV (.node [.phi e f]) = true := by
      simp only [nfV, nfL, hq, Bool.and_true]; rfl
    rcases hle with hlt | heq
    · apply Acc.inv hb
      show ltVN _ _ = true
      simp only [ltVN, hn, ltV_node, ltL_eq, Ordinal.llt, hlt, Bool.true_or, Bool.true_and]
    · subst heq
      match m with
      | [] => exact hb
      | s :: m' =>
        apply Acc.inv hb
        show ltVN _ _ = true
        simp only [ltVN, hn, ltV_node, ltL_eq, Ordinal.llt, decide_true, Bool.true_and,
          Bool.or_true]

/-- **Schütte's argument**: `φ(a,b)` is accessible whenever `a` and `b` are. The
proof inducts on `a`, then on `b`, then on the size of the predecessor, and only
follows the case split in the definition of `ltP`. -/
theorem acc_phi {a : V} (ha : AccV a) : ∀ {b : V}, AccV b → AccP (.phi a b) := by
  induction ha with
  | intro a _ iha =>
  intro b hb
  induction hb with
  | intro b hbacc ihb =>
  have hb : AccV b := Acc.intro b hbacc
  suffices H : ∀ (h : Nat) (q : P), q.size ≤ h → ltPN q (.phi a b) = true → AccP q from
    Acc.intro _ fun q hq => H q.size q (Nat.le_refl _) hq
  intro h
  induction h with
  | zero =>
    intro q hqs _
    cases q; simp only [P.size] at hqs; exact absurd hqs (by omega)
  | succ h ihh =>
    intro q hqs hq
    match q, hqs, hq with
    | .phi e f, hqs, hq =>
      simp only [ltPN, nfP, Bool.and_eq_true] at hq
      obtain ⟨⟨hne, hnf⟩, hlt⟩ := hq
      rw [ltP] at hlt
      by_cases h1 : ltV e a = true
      · rw [ite_eq_left h1] at hlt
        have hf : AccV f := by
          match f, hlt, hnf, hqs with
          | .node [], _, _, _ => exact accV_zero
          | .node (p :: l), hlt, hnf, hqs =>
            rw [ltVP] at hlt
            apply accV_of_head _ hnf
            apply ihh p
            · simp only [P.size, V.size, sizeL] at hqs; omega
            · have hp : nfP p = true := by
                simp only [nfV, nfL, Bool.and_eq_true] at hnf; exact hnf.2.1
              simp only [ltPN, hp, hlt, Bool.and_self]
        exact iha e (by simp only [LT', ltVN, hne, h1, Bool.and_self]) hf
      · rw [ite_eq_right h1] at hlt
        by_cases h2 : e = a
        · subst h2
          rw [ite_eq_left (decide_eq_true rfl)] at hlt
          exact ihb f (by simp only [LT', ltVN, hnf, hlt, Bool.and_self])
        · rw [ite_eq_right (by simpa using h2)] at hlt
          exact accP_of_le hb (by simp only [nfP, hne, hnf, Bool.and_self]) hlt

/-- **Every normal term is accessible.** -/
theorem acc_nf : ∀ x : V, nfV x = true → AccV x
  | .node [], _ => accV_zero
  | .node (.phi a b :: l), h => by
      have h' := h
      simp only [nfV, nfL, nfP, Bool.and_eq_true] at h'
      exact accV_of_head (acc_phi (acc_nf a h'.2.1.1) (acc_nf b h'.2.1.2)) h
termination_by x => x.size
decreasing_by all_goals simp only [V.size, sizeL, P.size]; omega

end Veblen

open Veblen in
/-- Notations for the ordinals below `Γ₀` (hereditarily sorted Veblen terms). -/
def Gamma0 : Type := {x : V // nfV x = true}

instance : DecidableEq Gamma0 := fun a b =>
  if h : a.1 = b.1 then isTrue (Subtype.ext h) else isFalse (fun e => h (congrArg Subtype.val e))

instance : FL.AtomOrder Gamma0 := ⟨fun a b => Veblen.ltV a.1 b.1⟩

theorem gamma0_wf : WellFounded (FL.ALt (α := Gamma0)) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨x, hx⟩ := a
  have h := Veblen.acc_nf x hx
  induction h with
  | intro x _ ih =>
    exact Acc.intro _ fun b hb => by
      obtain ⟨y, hy⟩ := b
      refine ih y ?_ hy
      show Veblen.ltVN y x = true
      simp only [Veblen.ltVN, hy, Bool.true_and]
      exact hb

/-- Veblen terms of height `≤ n` with at most `n` summands per sum. -/
def vsUpTo : Nat → List Veblen.V
  | 0 => []
  | n + 1 =>
      let vs := vsUpTo n
      (listsOf (vs.flatMap fun a => vs.map fun b => Veblen.P.phi a b) n).map Veblen.V.node

/-- Atoms of enumeration depth `n`: the normal terms among `vsUpTo n`. -/
def gamma0UpTo (n : Nat) : List Gamma0 :=
  (vsUpTo n).filterMap fun x => if h : Veblen.nfV x = true then some ⟨x, h⟩ else none

end BusyLean.Ordinal
