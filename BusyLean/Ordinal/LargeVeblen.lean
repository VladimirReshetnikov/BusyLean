import BusyLean.Ordinal.SortedLexQ
import BusyLean.Ordinal.Epsilon0

/-!
# Atoms below the large Veblen ordinal

Schütte's *Klammersymbole*. A principal term is `φ(A)`, where the argument
array `A` is a list of entries `(position, value)` sorted by decreasing
position. **Positions are themselves terms**. Terms are sums of principal
terms. Arrays are compared lexicographically by entries, an entry being
`(position, value)` ordered lexicographically: this is the first-difference
order at the most significant position. Principal terms follow the generalized
Veblen rule:

* `φ(A) < φ(B)` if `A < B` and every value of `A` is below `φ(B)`;
* otherwise, if `A ≠ B`, `φ(A) < φ(B)` if `φ(A) ≤` some value of `B`.

Binary Veblen is the case of positions `0` and `1`. With term positions, the
genuine normal forms reach the large Veblen ordinal.

Well-foundedness again follows only the case split of the Boolean comparison.
An entry is *good* when it is normal and its position and value are
accessible. Good entries are accessible (`accE`), so sorted arrays of good
entries are accessible (`accQ_sorted`). `acc_phi` inducts on the array, then
on the size of the predecessor:

* in the first case, the predecessor's values are accessible by the size
  induction, and its positions are accessible because they lie below
  positions of `A` (`posAcc`), so its array is a smaller good array;
* in the second case, the predecessor lies below a value of `A`.
-/

namespace BusyLean.Ordinal

namespace LVeblen

mutual
/-- Sums `node [p₁, …, p_k]` of principal terms. -/
inductive V where
  | node : List P → V
/-- Principal terms `φ(A)`. -/
inductive P where
  | phi : List E → P
/-- Array entries `(position, value)`. -/
inductive E where
  | entry : V → V → E
end

mutual
def decEqV : (x y : V) → Decidable (x = y)
  | .node l, .node m =>
      match decEqLP l m with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (V.node.inj e)

def decEqP : (p q : P) → Decidable (p = q)
  | .phi A, .phi B =>
      match decEqLE A B with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (P.phi.inj e)

def decEqE : (e f : E) → Decidable (e = f)
  | .entry a b, .entry c d =>
      match decEqV a c, decEqV b d with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun e => h₁ (E.entry.inj e).1
      | _, isFalse h₂ => isFalse fun e => h₂ (E.entry.inj e).2

def decEqLP : (l m : List P) → Decidable (l = m)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun e => nomatch e
  | _ :: _, [] => isFalse fun e => nomatch e
  | p :: l, q :: m =>
      match decEqP p q, decEqLP l m with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun e => h₁ (List.cons.inj e).1
      | _, isFalse h₂ => isFalse fun e => h₂ (List.cons.inj e).2

def decEqLE : (l m : List E) → Decidable (l = m)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun e => nomatch e
  | _ :: _, [] => isFalse fun e => nomatch e
  | p :: l, q :: m =>
      match decEqE p q, decEqLE l m with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun e => h₁ (List.cons.inj e).1
      | _, isFalse h₂ => isFalse fun e => h₂ (List.cons.inj e).2
end

instance : DecidableEq V := decEqV
instance : DecidableEq P := decEqP
instance : DecidableEq E := decEqE

def E.pos : E → V
  | .entry p _ => p
def E.val : E → V
  | .entry _ x => x

mutual
def V.size : V → Nat
  | .node l => 1 + sizeLP l
def sizeLP : List P → Nat
  | [] => 0
  | p :: l => 1 + p.size + sizeLP l
def P.size : P → Nat
  | .phi A => 1 + sizeLE A
def sizeLE : List E → Nat
  | [] => 0
  | e :: A => 1 + e.size + sizeLE A
def E.size : E → Nat
  | .entry p x => 1 + p.size + x.size
end

mutual
/-- The order on sums. -/
def ltV : V → V → Bool
  | .node l, .node m => ltLP l m
termination_by x y => x.size + y.size
decreasing_by all_goals simp only [V.size]; omega

def ltLP : List P → List P → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | p :: l, q :: m => ltP p q || (decide (p = q) && ltLP l m)
termination_by l m => sizeLP l + sizeLP m
decreasing_by all_goals simp only [sizeLP]; omega

/-- The generalized Veblen rule. -/
def ltP : P → P → Bool
  | .phi A, .phi B =>
      if arrLt A B then allLt A B
      else if decide (A = B) then false
      else anyGe A B
termination_by p q => p.size + q.size
decreasing_by all_goals simp only [P.size]; omega

/-- Entries: position first, then value. -/
def ltE : E → E → Bool
  | .entry p x, .entry q y => ltV p q || (decide (p = q) && ltV x y)
termination_by e f => e.size + f.size
decreasing_by all_goals simp only [E.size]; omega

/-- Arrays: lexicographic by entries. -/
def arrLt : List E → List E → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | e :: A, f :: B => ltE e f || (decide (e = f) && arrLt A B)
termination_by A B => sizeLE A + sizeLE B
decreasing_by all_goals simp only [sizeLE]; omega

/-- Every value of `A` is below `φ(B)`. -/
def allLt : List E → List E → Bool
  | [], _ => true
  | .entry _ x :: A, B => ltVP x B && allLt A B
termination_by A B => sizeLE A + sizeLE B + 1
decreasing_by all_goals simp only [sizeLE, E.size]; omega

/-- Some value of `B` is at least `φ(A)`. -/
def anyGe : List E → List E → Bool
  | _, [] => false
  | A, .entry _ y :: B => leVP A y || anyGe A B
termination_by A B => sizeLE A + sizeLE B + 1
decreasing_by all_goals simp only [sizeLE, E.size]; omega

/-- `x < φ(B)`. -/
def ltVP : V → List E → Bool
  | .node [], _ => true
  | .node (p :: _), B => ltP p (.phi B)
termination_by x B => x.size + sizeLE B + 1
decreasing_by all_goals simp only [V.size, sizeLP, P.size]; omega

/-- `φ(A) ≤ y`. -/
def leVP : List E → V → Bool
  | _, .node [] => false
  | A, .node (q :: _) => ltP (.phi A) q || decide (P.phi A = q)
termination_by A y => sizeLE A + y.size + 1
decreasing_by all_goals simp only [V.size, sizeLP, P.size]; omega
end

mutual
/-- Normal terms: sums non-increasing and arrays sorted, hereditarily. -/
def nfV : V → Bool
  | .node l => sorted ltP l && nfLP l
def nfLP : List P → Bool
  | [] => true
  | p :: l => nfP p && nfLP l
def nfP : P → Bool
  | .phi A => sorted ltE A && nfLE A
def nfLE : List E → Bool
  | [] => true
  | e :: A => nfE e && nfLE A
def nfE : E → Bool
  | .entry p x => nfV p && nfV x
end

def ltPN (p q : P) : Bool := nfP p && ltP p q
def ltVN (x y : V) : Bool := nfV x && ltV x y

abbrev AccV := Acc (LT' ltVN)
abbrev AccP := Acc (LT' ltPN)

/-- Good entries: normal, with accessible position and value. -/
def QE (e : E) : Prop := nfE e = true ∧ AccV e.pos ∧ AccV e.val

theorem ltLP_eq : ∀ l m : List P, ltLP l m = Ordinal.llt ltP l m
  | [], [] => by rw [ltLP]; rfl
  | [], _ :: _ => by rw [ltLP]; rfl
  | _ :: _, [] => by rw [ltLP]; rfl
  | p :: l, q :: m => by rw [ltLP, ltLP_eq l m]; rfl

theorem arrLt_eq : ∀ A B : List E, arrLt A B = Ordinal.llt ltE A B
  | [], [] => by rw [arrLt]; rfl
  | [], _ :: _ => by rw [arrLt]; rfl
  | _ :: _, [] => by rw [arrLt]; rfl
  | e :: A, f :: B => by rw [arrLt, arrLt_eq A B]; rfl

theorem llt_ltPN : ∀ l m : List P, nfLP l = true → Ordinal.llt ltPN l m = Ordinal.llt ltP l m
  | [], [] , _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: l, q :: m, h => by
      simp only [nfLP, Bool.and_eq_true] at h
      simp only [Ordinal.llt, ltPN, h.1, Bool.true_and, llt_ltPN l m h.2]

theorem sorted_ltPN : ∀ l : List P, nfLP l = true → sorted ltP l = true → sorted ltPN l = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: t, ha, hs => by
      simp only [nfLP, Bool.and_eq_true] at ha
      have hst := sorted_tail hs
      simp only [sorted, Bool.and_eq_true] at hs ⊢
      refine ⟨?_, sorted_ltPN (y :: t) (by simp only [nfLP, Bool.and_eq_true]; exact ha.2) hst⟩
      have h1 := hs.1
      simp only [Ordinal.le, Bool.or_eq_true] at h1 ⊢
      rcases h1 with h1 | h1
      · exact Or.inl (by simp only [ltPN, ha.2.1, h1, Bool.and_self])
      · exact Or.inr h1

theorem ltV_node (l m : List P) : ltV (.node l) (.node m) = ltLP l m := by rw [ltV]

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
      rw [llt_ltPN m l ha, ← ltLP_eq, ← ltV_node]
      exact hlt

theorem accV_zero : AccV (.node []) :=
  Acc.intro _ fun x hx => by
    match x, hx with
    | .node m, hx =>
      simp only [LT', ltVN, ltV_node, Bool.and_eq_true] at hx
      have := hx.2
      rw [ltLP_eq, llt_nil_right] at this
      cases this

theorem accV_of_head {p : P} {l : List P} (hp : AccP p) (hn : nfV (.node (p :: l)) = true) :
    AccV (.node (p :: l)) := by
  simp only [nfV, Bool.and_eq_true] at hn
  exact acc_of_children _ (acc_head hp (p :: l) (sorted_ltPN _ hn.2 hn.1) rfl)

theorem accP_of_single {p : P} (h : AccV (.node [p])) : AccP p := by
  generalize hx : V.node [p] = x at h
  induction h generalizing p with
  | intro x _ ih =>
    subst hx
    refine Acc.intro _ fun q hq => ?_
    simp only [LT', ltPN, Bool.and_eq_true] at hq
    refine ih (.node [q]) ?_ rfl
    show ltVN (.node [q]) (.node [p]) = true
    simp only [ltVN, nfV, nfLP, hq.1, ltV_node, ltLP_eq, Ordinal.llt, hq.2, Bool.true_or,
      Bool.and_true]
    rfl

/-- If `φ(A) ≤ y` and `y` is accessible, then `φ(A)` is accessible. -/
theorem accP_of_le {A : List E} {y : V} (hy : AccV y) (hq : nfP (.phi A) = true)
    (hle : leVP A y = true) : AccP (.phi A) := by
  match y, hy, hle with
  | .node [], _, hle => rw [leVP] at hle; cases hle
  | .node (r :: m), hy, hle =>
    rw [leVP] at hle
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hle
    apply accP_of_single
    have hn : nfV (.node [.phi A]) = true := by
      simp only [nfV, nfLP, hq, Bool.and_true]; rfl
    rcases hle with hlt | heq
    · apply Acc.inv hy
      show ltVN _ _ = true
      simp only [ltVN, hn, ltV_node, ltLP_eq, Ordinal.llt, hlt, Bool.true_or, Bool.true_and]
    · subst heq
      match m with
      | [] => exact hy
      | s :: m' =>
        apply Acc.inv hy
        show ltVN _ _ = true
        simp only [ltVN, hn, ltV_node, ltLP_eq, Ordinal.llt, decide_true, Bool.true_and,
          Bool.or_true]

/-- Good entries are accessible: induction on the position, then the value. -/
theorem accE_aux {p : V} (hp : AccV p) : ∀ {x : V}, AccV x → nfE (.entry p x) = true →
    Acc (LTQ QE ltE) (.entry p x) := by
  induction hp with
  | intro p _ ihp =>
  intro x hx
  induction hx with
  | intro x _ ihx =>
  intro _
  refine Acc.intro _ fun f ⟨⟨hnf, hqp, hqv⟩, hlt⟩ => ?_
  match f, hnf, hqp, hqv, hlt with
  | .entry q y, hnf, hqp, hqv, hlt =>
    have hn := hnf
    simp only [nfE, Bool.and_eq_true] at hn
    rw [ltE] at hlt
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt
    rcases hlt with h1 | ⟨rfl, h2⟩
    · exact ihp q (by simp only [LT', ltVN, hn.1, h1, Bool.and_self]) hqv hnf
    · exact ihx y (by simp only [LT', ltVN, hn.2, h2, Bool.and_self]) hnf

theorem accE : ∀ e : E, QE e → Acc (LTQ QE ltE) e
  | .entry _ _, ⟨hn, hp, hx⟩ => accE_aux hp hx hn

theorem le_ltE {f e : E} (h : Ordinal.le ltE f e = true) :
    ltV f.pos e.pos = true ∨ f.pos = e.pos := by
  simp only [Ordinal.le, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | rfl
  · match f, e, h with
    | .entry q y, .entry p x, h =>
      rw [ltE] at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
  · exact Or.inr rfl

/-- In a sorted array, positions decrease, so they are accessible when the first one is. -/
theorem chainAcc : ∀ (g : E) (Γ : List E), sorted ltE (g :: Γ) = true → nfLE (g :: Γ) = true →
    AccV g.pos → ∀ e ∈ g :: Γ, AccV e.pos
  | g, [], _, _, hg, e, he => by
      rcases List.mem_cons.1 he with rfl | he
      · exact hg
      · cases he
  | g, g₂ :: Γ, hs, hn, hg, e, he => by
      have hst := sorted_tail hs
      have hn₂ : nfLE (g₂ :: Γ) = true := by
        simp only [nfLE, Bool.and_eq_true] at hn ⊢; exact hn.2
      have hg₂ : AccV g₂.pos := by
        simp only [sorted, Bool.and_eq_true] at hs
        rcases le_ltE hs.1 with h | h
        · apply Acc.inv hg
          have : nfV g₂.pos = true := by
            match g₂, hn₂ with
            | .entry q y, hn₂ =>
              simp only [nfLE, nfE, Bool.and_eq_true] at hn₂; exact hn₂.1.1
          show ltVN _ _ = true
          simp only [ltVN, this, h, Bool.and_self]
        · rw [h]; exact hg
      rcases List.mem_cons.1 he with rfl | he
      · exact hg
      · exact chainAcc g₂ Γ hst hn₂ hg₂ e he

/-- Positions of a smaller sorted array lie below positions of the larger one. -/
theorem posAcc : ∀ (Γ A : List E), (∀ e ∈ A, AccV e.pos) → nfLE Γ = true →
    sorted ltE Γ = true → arrLt Γ A = true → ∀ e ∈ Γ, AccV e.pos
  | [], _, _, _, _, _, e, he => by cases he
  | _ :: _, [], _, _, _, h, _, _ => by rw [arrLt] at h; cases h
  | g :: Γ, a :: A, hA, hn, hs, h, e, he => by
      rw [arrLt] at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      have ha : AccV a.pos := hA a List.mem_cons_self
      rcases h with h | ⟨rfl, h⟩
      · have hg : AccV g.pos := by
          have := le_ltE (f := g) (e := a) (by simp only [Ordinal.le, h, Bool.true_or])
          rcases this with h' | h'
          · apply Acc.inv ha
            have : nfV g.pos = true := by
              match g, hn with
              | .entry q y, hn =>
                simp only [nfLE, nfE, Bool.and_eq_true] at hn; exact hn.1.1
            show ltVN _ _ = true
            simp only [ltVN, this, h', Bool.and_self]
          · rw [h']; exact ha
        exact chainAcc g Γ hs hn hg e he
      · rcases List.mem_cons.1 he with rfl | he
        · exact ha
        · have hn' : nfLE Γ = true := by simp only [nfLE, Bool.and_eq_true] at hn; exact hn.2
          exact posAcc Γ A (fun e he => hA e (List.mem_cons_of_mem _ he)) hn' (sorted_tail hs) h e he

theorem allLt_mem : ∀ {Γ B : List E}, allLt Γ B = true → ∀ e ∈ Γ, ltVP e.val B = true
  | [], _, _, e, he => by cases he
  | .entry _ x :: Γ, B, h, e, he => by
      rw [allLt] at h
      simp only [Bool.and_eq_true] at h
      rcases List.mem_cons.1 he with rfl | he
      · exact h.1
      · exact allLt_mem h.2 e he

theorem anyGe_mem : ∀ {Γ B : List E}, anyGe Γ B = true → ∃ e ∈ B, leVP Γ e.val = true
  | _, [], h => by rw [anyGe] at h; cases h
  | Γ, .entry _ y :: B, h => by
      rw [anyGe] at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨e, he, h⟩ := anyGe_mem h
        exact ⟨e, List.mem_cons_of_mem _ he, h⟩

theorem size_val_lt : ∀ {Γ : List E} {e : E}, e ∈ Γ → e.val.size + 2 ≤ (P.phi Γ).size
  | f :: Γ, e, he => by
      rcases List.mem_cons.1 he with rfl | he
      · match e with
        | .entry p x => simp only [E.val, P.size, sizeLE, E.size]; omega
      · have := size_val_lt (Γ := Γ) he
        simp only [P.size, sizeLE] at this ⊢; omega

theorem nfE_of_mem : ∀ {Γ : List E} {e : E}, nfLE Γ = true → e ∈ Γ → nfE e = true
  | f :: Γ, e, hn, he => by
      simp only [nfLE, Bool.and_eq_true] at hn
      rcases List.mem_cons.1 he with rfl | he
      · exact hn.1
      · exact nfE_of_mem hn.2 he

/-- **The generalized Veblen step**: `φ(A)` is accessible for every accessible
array of good entries. -/
theorem acc_phi : ∀ (A : List E), Acc (SRQ QE ltE) A → (∀ e ∈ A, QE e) → AccP (.phi A) := by
  intro A hA
  induction hA with
  | intro A _ ihA =>
  intro hQ
  suffices H : ∀ (h : Nat) (q : P), q.size ≤ h → ltPN q (.phi A) = true → AccP q from
    Acc.intro _ fun q hq => H q.size q (Nat.le_refl _) hq
  intro h
  induction h with
  | zero =>
    intro q hqs _
    cases q; simp only [P.size] at hqs; exact absurd hqs (by omega)
  | succ h ihh =>
    intro q hqs hq
    match q, hqs, hq with
    | .phi Γ, hqs, hq =>
      simp only [ltPN, Bool.and_eq_true] at hq
      obtain ⟨hnP, hlt⟩ := hq
      have hnP' := hnP
      simp only [nfP, Bool.and_eq_true] at hnP'
      obtain ⟨hsΓ, hnΓ⟩ := hnP'
      rw [ltP] at hlt
      by_cases h1 : arrLt Γ A = true
      · rw [ite_eq_left h1] at hlt
        -- values of Γ are accessible by the size induction
        have hval : ∀ e ∈ Γ, AccV e.val := by
          intro e he
          have hv := allLt_mem hlt e he
          have hsz := size_val_lt he
          have hne := nfE_of_mem hnΓ he
          match e, hv, hsz, hne with
          | .entry pos val, hv, hsz, hne =>
            simp only [E.val] at hv hsz ⊢
            match val, hv, hsz, hne with
            | .node [], _, _, _ => exact accV_zero
            | .node (p :: l), hv, hsz, hne =>
              rw [ltVP] at hv
              have hnv : nfV (.node (p :: l)) = true := by
                simp only [nfE, Bool.and_eq_true] at hne; exact hne.2
              apply accV_of_head _ hnv
              apply ihh p
              · simp only [V.size, sizeLP] at hsz; omega
              · have hp : nfP p = true := by
                  simp only [nfV, nfLP, Bool.and_eq_true] at hnv; exact hnv.2.1
                simp only [ltPN, hp, hv, Bool.and_self]
        have hpos : ∀ e ∈ Γ, AccV e.pos :=
          posAcc Γ A (fun e he => (hQ e he).2.1) hnΓ hsΓ h1
        have hQΓ : ∀ e ∈ Γ, QE e := fun e he => ⟨nfE_of_mem hnΓ he, hpos e he, hval e he⟩
        exact ihA Γ ⟨hQΓ, hsΓ, by rw [← arrLt_eq]; exact h1⟩ hQΓ
      · rw [ite_eq_right h1] at hlt
        by_cases h2 : Γ = A
        · subst h2; rw [ite_eq_left (decide_eq_true rfl)] at hlt; cases hlt
        · rw [ite_eq_right (by simpa using h2)] at hlt
          obtain ⟨e, he, hle⟩ := anyGe_mem hlt
          exact accP_of_le (hQ e he).2.2 hnP hle

mutual
/-- **Every normal term is accessible.** -/
theorem acc_nf : ∀ x : V, nfV x = true → AccV x
  | .node [], _ => accV_zero
  | .node (.phi A :: l), h => by
      have h' := h
      simp only [nfV, nfLP, nfP, Bool.and_eq_true] at h'
      have hQ := goodEntries A h'.2.1.2
      exact accV_of_head (acc_phi A (accQ_sorted accE A hQ h'.2.1.1) hQ) h
termination_by x => x.size
decreasing_by all_goals simp only [V.size, sizeLP, P.size]; omega

theorem goodEntries : ∀ A : List E, nfLE A = true → ∀ e ∈ A, QE e
  | [], _, e, he => by cases he
  | .entry p x :: A, h, e, he => by
      have h' := h
      simp only [nfLE, nfE, Bool.and_eq_true] at h'
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨by simp only [nfE, h'.1.1, h'.1.2, Bool.and_self], acc_nf p h'.1.1, acc_nf x h'.1.2⟩
      · exact goodEntries A h'.2 e he
termination_by A => sizeLE A
decreasing_by all_goals simp only [sizeLE, E.size]; omega
end

end LVeblen

open LVeblen in
/-- Notations for the ordinals below the large Veblen ordinal. -/
def LargeVeblen : Type := {x : V // nfV x = true}

instance : DecidableEq LargeVeblen := fun a b =>
  if h : a.1 = b.1 then isTrue (Subtype.ext h) else isFalse (fun e => h (congrArg Subtype.val e))

instance : FL.AtomOrder LargeVeblen := ⟨fun a b => LVeblen.ltV a.1 b.1⟩

theorem largeVeblen_wf : WellFounded (FL.ALt (α := LargeVeblen)) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨x, hx⟩ := a
  have h := LVeblen.acc_nf x hx
  induction h with
  | intro x _ ih =>
    exact Acc.intro _ fun b hb => by
      obtain ⟨y, hy⟩ := b
      refine ih y ?_ hy
      show LVeblen.ltVN y x = true
      simp only [LVeblen.ltVN, hy, Bool.true_and]
      exact hb

/-- Terms of height `≤ n` with at most `n` summands and `n` entries per array. -/
def lvsUpTo : Nat → List LVeblen.V
  | 0 => []
  | n + 1 =>
      let vs := lvsUpTo n
      let es := vs.flatMap fun p => vs.map fun x => LVeblen.E.entry p x
      let ps := (listsOf es n).map LVeblen.P.phi
      (listsOf ps n).map LVeblen.V.node

/-- Atoms of enumeration depth `n`: the normal terms among `lvsUpTo n`. -/
def largeVeblenUpTo (n : Nat) : List LargeVeblen :=
  (lvsUpTo n).filterMap fun x => if h : LVeblen.nfV x = true then some ⟨x, h⟩ else none

end BusyLean.Ordinal
