import BusyLean.Ordinal.SortedLexQ
import BusyLean.Ordinal.Epsilon0

/-!
# Atoms below the Bachmann–Howard ordinal

Buchholz-style collapsing notation with two levels. Terms are sums of principal
terms `D₀ a` (`ψ₀(a)`, countable) and `D₁ a` (`ψ₁(a)`, at least `Ω`). Principal
terms are compared lexicographically, level first, and sums lexicographically.
Every `D₁` term lies above every `D₀` term.

The raw order is *not* well-founded: `D₁0 > D₀D₁0 > D₀D₀D₁0 > ⋯`. Normal forms
fix this. `Dᵤ a` is normal when `a` is normal and every element of `Gᵤ(a)` is
below `a`, where `Gᵤ(D_v b) = ∅` if `v < u` and `{b} ∪ Gᵤ(b)` otherwise. Here
`D₀D₁0` is normal, but `D₀D₀D₁0` is not, because `D₁0 ∈ G₀(D₀D₁0)` is not below
`D₀D₁0`. The normal forms reach `ψ₀(ε_{Ω+1})`, the Bachmann–Howard ordinal.

The well-foundedness proof is the classical impredicative argument:

* `M` is the set of terms whose *top-level `D₀`-components* (reached through
  sums and `D₁` only) are accessible.
* **Claim 1** (`accM_V`): the order restricted to `M` is well-founded. This is
  predicative: `D₀` components are accessible by assumption, and `D₁` terms
  and sums are handled by induction.
* **Claim 2** (`accD0`): if `a ∈ M`, then `D₀ a` is accessible, by induction on
  `a` in `M`. A predecessor `D₀ c` has `c < a`, and `c ∈ M` because its `D₀`
  components `D₀ f` have `f < c < a` (normality, then **transitivity**) and are
  smaller, so an inner size induction applies.
* **Claim 3**: every `D₀ c` is accessible (size induction plus Claims 1–2),
  every `D₁ b` with accessible `b` is accessible, and hence every normal term.
-/

namespace BusyLean.Ordinal

namespace BH

mutual
/-- Sums `node [p₁, …, p_k]` of principal terms. -/
inductive V where
  | node : List P → V
/-- Principal terms `D u a`, with level `u` (`false` = 0, `true` = 1). -/
inductive P where
  | D : Bool → V → P
end

mutual
def decEqV : (x y : V) → Decidable (x = y)
  | .node l, .node m =>
      match decEqL l m with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (V.node.inj e)

def decEqP : (p q : P) → Decidable (p = q)
  | .D u a, .D v b =>
      if hu : u = v then
        match decEqV a b with
        | isTrue h => isTrue (hu ▸ h ▸ rfl)
        | isFalse h => isFalse fun e => h (P.D.inj e).2
      else isFalse fun e => hu (P.D.inj e).1

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

/-- Levels: `0 < 1`. -/
def ltLev (u v : Bool) : Bool := !u && v

mutual
def ltV : V → V → Bool
  | .node l, .node m => ltL l m
def ltL : List P → List P → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | p :: l, q :: m => ltP p q || (decide (p = q) && ltL l m)
def ltP : P → P → Bool
  | .D u a, .D v b => ltLev u v || (decide (u = v) && ltV a b)
end

mutual
/-- `Gᵤ`, as a list. -/
def gListV (u : Bool) : V → List V
  | .node l => gListL u l
def gListL (u : Bool) : List P → List V
  | [] => []
  | p :: l => gListP u p ++ gListL u l
def gListP (u : Bool) : P → List V
  | .D v b => if ltLev v u then [] else b :: gListV u b
end

mutual
/-- Arguments of the top-level `D₀` components (reached through sums and `D₁`). -/
def kListV : V → List V
  | .node l => kListL l
def kListL : List P → List V
  | [] => []
  | p :: l => kListP p ++ kListL l
def kListP : P → List V
  | .D false f => [f]
  | .D true b => kListV b
end

mutual
/-- Normal forms: sums non-increasing, and `Dᵤ a` only when `Gᵤ(a) < a`. -/
def nfV : V → Bool
  | .node l => sorted ltP l && nfL l
def nfL : List P → Bool
  | [] => true
  | p :: l => nfP p && nfL l
def nfP : P → Bool
  | .D u a => nfV a && (gListV u a).all (fun b => ltV b a)
end

mutual
def V.size : V → Nat
  | .node l => 1 + sizeL l
def sizeL : List P → Nat
  | [] => 0
  | p :: l => 1 + p.size + sizeL l
def P.size : P → Nat
  | .D _ a => 1 + a.size
end

def ltPN (p q : P) : Bool := nfP p && ltP p q
def ltVN (x y : V) : Bool := nfV x && ltV x y

abbrev AccV := Acc (LT' ltVN)
abbrev AccP := Acc (LT' ltPN)

/-! ## Transitivity (structural) -/

mutual
theorem ltV_trans : ∀ x y z : V, ltV x y = true → ltV y z = true → ltV x z = true
  | .node l, .node m, .node n, h₁, h₂ => ltL_trans l m n h₁ h₂
theorem ltL_trans : ∀ l m n : List P, ltL l m = true → ltL m n = true → ltL l n = true
  | [], [], _, h, _ => by simp only [ltL] at h; cases h
  | [], _ :: _, [], _, h => by simp only [ltL] at h; cases h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp only [ltL] at h; cases h
  | _ :: _, _ :: _, [], _, h => by simp only [ltL] at h; cases h
  | p :: l, q :: m, r :: n, h₁, h₂ => by
      simp only [ltL, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
      rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
      · exact Or.inl (ltP_trans p q r h₁ h₂)
      · exact Or.inl h₁
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, ltL_trans l m n h₁ h₂⟩
theorem ltP_trans : ∀ p q r : P, ltP p q = true → ltP q r = true → ltP p r = true
  | .D u a, .D v b, .D w c, h₁, h₂ => by
      simp only [ltP, ltLev, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at h₁ h₂ ⊢
      rcases h₁ with ⟨hu, hv⟩ | ⟨rfl, h₁⟩ <;> rcases h₂ with ⟨hv', hw⟩ | ⟨rfl, h₂⟩
      · subst hv; cases hv'
      · exact Or.inl ⟨hu, hv⟩
      · exact Or.inl ⟨hv', hw⟩
      · exact Or.inr ⟨rfl, ltV_trans a b c h₁ h₂⟩
end

/-! ## Sums -/

theorem ltL_eq : ∀ l m : List P, ltL l m = Ordinal.llt ltP l m
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: l, q :: m => by simp only [ltL, Ordinal.llt, ltL_eq l m]

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

theorem acc_of_children : ∀ l : List P, Acc (SR ltPN) l → AccV (.node l) := by
  intro l hl
  induction hl with
  | intro l _ ih =>
    refine Acc.intro _ fun x hx => ?_
    match x, hx with
    | .node m, hx =>
      simp only [LT', ltVN, nfV, ltV, Bool.and_eq_true] at hx
      obtain ⟨⟨hs, ha⟩, hlt⟩ := hx
      refine ih m ⟨sorted_ltPN m ha hs, ?_⟩
      rw [llt_ltPN m l ha, ← ltL_eq]
      exact hlt

theorem accV_zero : AccV (.node []) :=
  Acc.intro _ fun x hx => by
    match x, hx with
    | .node m, hx =>
      simp only [LT', ltVN, ltV, Bool.and_eq_true] at hx
      have := hx.2
      rw [ltL_eq, llt_nil_right] at this
      cases this

theorem accV_of_head {p : P} {l : List P} (hp : AccP p) (hn : nfV (.node (p :: l)) = true) :
    AccV (.node (p :: l)) := by
  simp only [nfV, Bool.and_eq_true] at hn
  exact acc_of_children _ (acc_head hp (p :: l) (sorted_ltPN _ hn.2 hn.1) rfl)

/-! ## Components -/

mutual
theorem mem_kListV : ∀ {c f : V}, f ∈ kListV c →
    f ∈ gListV false c ∧ f.size < c.size ∧ (nfV c = true → nfP (.D false f) = true)
  | .node l, f, h => by
      have := mem_kListL (l := l) h
      simp only [V.size]
      exact ⟨this.1, by omega, fun hn => this.2.2 (by simp only [nfV, Bool.and_eq_true] at hn; exact hn.2)⟩
termination_by c => c.size
decreasing_by all_goals simp only [V.size]; omega
theorem mem_kListL : ∀ {l : List P} {f : V}, f ∈ kListL l →
    f ∈ gListL false l ∧ f.size < sizeL l ∧ (nfL l = true → nfP (.D false f) = true)
  | [], f, h => by cases h
  | p :: l, f, h => by
      simp only [kListL, List.mem_append] at h
      simp only [gListL, List.mem_append, sizeL, nfL, Bool.and_eq_true]
      rcases h with h | h
      · have := mem_kListP h
        exact ⟨Or.inl this.1, by omega, fun hn => this.2.2 hn.1⟩
      · have := mem_kListL h
        exact ⟨Or.inr this.1, by omega, fun hn => this.2.2 hn.2⟩
termination_by l => sizeL l
decreasing_by all_goals simp only [sizeL]; omega
theorem mem_kListP : ∀ {p : P} {f : V}, f ∈ kListP p →
    f ∈ gListP false p ∧ f.size < p.size ∧ (nfP p = true → nfP (.D false f) = true)
  | .D false g, f, h => by
      simp only [kListP, List.mem_singleton] at h
      subst h
      simp only [gListP, ltLev, Bool.not_false, Bool.and_false, P.size]
      exact ⟨List.mem_cons_self, by omega, id⟩
  | .D true b, f, h => by
      simp only [kListP] at h
      have := mem_kListV h
      refine ⟨?_, ?_, ?_⟩
      · simp only [gListP, ltLev, Bool.not_true, Bool.false_and]
        exact List.mem_cons_of_mem _ this.1
      · simp only [P.size]; omega
      · intro hn
        apply this.2.2
        simp only [nfP, Bool.and_eq_true] at hn
        exact hn.1
termination_by p => p.size
decreasing_by all_goals simp only [P.size]; omega
end

/-! ## The good part `M` -/

/-- Terms whose top-level `D₀` components are accessible. -/
def MV (x : V) : Prop := ∀ f ∈ kListV x, AccP (.D false f)
def MP (p : P) : Prop := ∀ f ∈ kListP p, AccP (.D false f)

def QV (x : V) : Prop := nfV x = true ∧ MV x
def QP (p : P) : Prop := nfP p = true ∧ MP p

theorem kListP_sub : ∀ {m : List P} {q : P} {f : V}, q ∈ m → f ∈ kListP q → f ∈ kListL m
  | _ :: m, q, f, hq, hf => by
      simp only [kListL, List.mem_append]
      rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl hf
      · exact Or.inr (kListP_sub hq hf)

theorem nfP_of_mem : ∀ {m : List P} {q : P}, q ∈ m → nfL m = true → nfP q = true
  | _ :: m, q, hq, hn => by
      simp only [nfL, Bool.and_eq_true] at hn
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hn.1
      · exact nfP_of_mem hq hn.2

theorem ltPN_of_LTQ {a b : P} (h : LTQ QP ltP a b) : LT' ltPN a b := by
  show ltPN a b = true
  simp only [ltPN, h.1.1, h.2, Bool.and_self]

/-- Sums of good principal terms inherit accessibility in `M`. -/
theorem transferM : ∀ l : List P, Acc (SRQ QP ltP) l → Acc (LTQ QV ltV) (.node l) := by
  intro l hl
  induction hl with
  | intro l _ ih =>
    refine Acc.intro _ fun y ⟨⟨hny, hmy⟩, hlt⟩ => ?_
    match y, hny, hmy, hlt with
    | .node m, hny, hmy, hlt =>
      have hn' := hny
      simp only [nfV, Bool.and_eq_true] at hn'
      refine ih m ⟨fun q hq => ⟨nfP_of_mem hq hn'.2, fun f hf => hmy f (kListP_sub hq hf)⟩,
        hn'.1, ?_⟩
      rw [← ltL_eq]; exact hlt

mutual
/-- **Claim 1** (principal terms): the order restricted to `M` is well-founded. -/
theorem accM_P : ∀ p : P, QP p → Acc (LTQ QP ltP) p
  | .D false f, ⟨_, hm⟩ =>
      Subrelation.accessible (fun h => ltPN_of_LTQ h) (hm f (by simp only [kListP, List.mem_singleton]))
  | .D true b, ⟨hn, hm⟩ => by
      have hnb : nfV b = true := by simp only [nfP, Bool.and_eq_true] at hn; exact hn.1
      have hb := accM_V b ⟨hnb, fun f hf => hm f (by simpa only [kListP] using hf)⟩
      clear hn hm hnb
      induction hb with
      | intro b _ ih =>
        refine Acc.intro _ fun x hx => ?_
        match x, hx with
        | .D false c, hx =>
          exact Subrelation.accessible (fun h => ltPN_of_LTQ h)
            (hx.1.2 c (by simp only [kListP, List.mem_singleton]))
        | .D true c, ⟨⟨hnc, hmc⟩, hlt⟩ =>
          simp only [ltP, ltLev, Bool.not_true, Bool.false_and, Bool.false_or, decide_true,
            Bool.true_and] at hlt
          have hnc' : nfV c = true := by simp only [nfP, Bool.and_eq_true] at hnc; exact hnc.1
          exact ih c ⟨⟨hnc', fun f hf => hmc f (by simpa only [kListP] using hf)⟩, hlt⟩
termination_by p => p.size
decreasing_by all_goals simp only [P.size]; omega

/-- **Claim 1** (sums). -/
theorem accM_V : ∀ x : V, QV x → Acc (LTQ QV ltV) x
  | .node [], _ => Acc.intro _ fun y ⟨_, h⟩ => by
      match y, h with
      | .node m, h => simp only [ltV, ltL_eq, llt_nil_right] at h; cases h
  | .node (p :: l), ⟨hn, hm⟩ => by
      have hn' := hn
      simp only [nfV, Bool.and_eq_true] at hn'
      have hq : ∀ q ∈ p :: l, QP q := fun q hq =>
        ⟨nfP_of_mem hq hn'.2, fun f hf => hm f (kListP_sub hq hf)⟩
      exact transferM _ (accQ_head_of_acc (accM_P p (hq p List.mem_cons_self))
        (hq p List.mem_cons_self) (p :: l) hq hn'.1 rfl)
termination_by x => x.size
decreasing_by all_goals simp only [V.size, sizeL]; omega
end

/-- **Claim 2**: `D₀ a` is accessible for every `a` accessible within `M`. -/
theorem accD0 : ∀ a : V, Acc (LTQ QV ltV) a → nfP (.D false a) = true → AccP (.D false a) := by
  intro a ha
  induction ha with
  | intro a _ iha =>
  intro _
  have key : ∀ (s : Nat) (c : V), c.size ≤ s → nfP (.D false c) = true → ltV c a = true →
      AccP (.D false c) := by
    intro s
    induction s with
    | zero => intro c hc; cases c; simp only [V.size] at hc; exact absurd hc (by omega)
    | succ s ihs =>
      intro c hcs hnc hca
      have hnc' := hnc
      simp only [nfP, Bool.and_eq_true, List.all_eq_true] at hnc'
      have hmc : MV c := fun f hf => by
        obtain ⟨hg, hsz, hnf⟩ := mem_kListV hf
        exact ihs f (by omega) (hnf hnc'.1) (ltV_trans f c a (hnc'.2 f hg) hca)
      exact iha c ⟨⟨hnc'.1, hmc⟩, hca⟩ hnc
  refine Acc.intro _ fun y hy => ?_
  match y, hy with
  | .D false c, hy =>
    simp only [LT', ltPN, ltP, ltLev, Bool.not_false, Bool.and_false, Bool.false_or, decide_true,
      Bool.true_and, Bool.and_eq_true] at hy
    exact key c.size c (Nat.le_refl _) hy.1 hy.2
  | .D true c, hy =>
    simp only [LT', ltPN, ltP, ltLev, Bool.not_true, Bool.false_and, Bool.false_or,
      Bool.and_eq_true, decide_eq_true_eq] at hy
    exact absurd hy.2.1 (by decide)

/-- **Claim 3a**: every normal `D₀ c` is accessible. -/
theorem acc_D0 : ∀ (s : Nat) (c : V), c.size ≤ s → nfP (.D false c) = true → AccP (.D false c) := by
  intro s
  induction s with
  | zero => intro c hc; cases c; simp only [V.size] at hc; exact absurd hc (by omega)
  | succ s ihs =>
    intro c hcs hnc
    have hnc' := hnc
    simp only [nfP, Bool.and_eq_true] at hnc'
    have hmc : MV c := fun f hf => by
      obtain ⟨_, hsz, hnf⟩ := mem_kListV hf
      exact ihs f (by omega) (hnf hnc'.1)
    exact accD0 c (accM_V c ⟨hnc'.1, hmc⟩) hnc

/-- **Claim 3b**: `D₁ b` is accessible when `b` is. -/
theorem acc_D1 {b : V} (hb : AccV b) : nfP (.D true b) = true → AccP (.D true b) := by
  induction hb with
  | intro b _ ih =>
  intro _
  refine Acc.intro _ fun y hy => ?_
  match y, hy with
  | .D false c, hy =>
    simp only [LT', ltPN, Bool.and_eq_true] at hy
    exact acc_D0 c.size c (Nat.le_refl _) hy.1
  | .D true c, hy =>
    have hy' := hy
    simp only [LT', ltPN, ltP, ltLev, Bool.not_true, Bool.false_and, Bool.false_or, decide_true,
      Bool.true_and, Bool.and_eq_true] at hy'
    have hnc : nfV c = true := by
      have := hy'.1; simp only [nfP, Bool.and_eq_true] at this; exact this.1
    exact ih c (by simp only [LT', ltVN, hnc, hy'.2, Bool.and_self]) hy'.1

/-- **Every normal term is accessible.** -/
theorem acc_nf : ∀ x : V, nfV x = true → AccV x
  | .node [], _ => accV_zero
  | .node (.D false c :: l), h => by
      have h' := h
      simp only [nfV, nfL, Bool.and_eq_true] at h'
      exact accV_of_head (acc_D0 c.size c (Nat.le_refl _) h'.2.1) h
  | .node (.D true b :: l), h => by
      have h' := h
      simp only [nfV, nfL, Bool.and_eq_true] at h'
      have hb : nfV b = true := by
        have := h'.2.1; simp only [nfP, Bool.and_eq_true] at this; exact this.1
      exact accV_of_head (acc_D1 (acc_nf b hb) h'.2.1) h
termination_by x => x.size
decreasing_by all_goals simp only [V.size, sizeL, P.size]; omega

end BH

open BH in
/-- Notations for the ordinals below the Bachmann–Howard ordinal. -/
def BachmannHoward : Type := {x : V // nfV x = true}

instance : DecidableEq BachmannHoward := fun a b =>
  if h : a.1 = b.1 then isTrue (Subtype.ext h) else isFalse (fun e => h (congrArg Subtype.val e))

instance : FL.AtomOrder BachmannHoward := ⟨fun a b => BH.ltV a.1 b.1⟩

theorem bachmannHoward_wf : WellFounded (FL.ALt (α := BachmannHoward)) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨x, hx⟩ := a
  have h := BH.acc_nf x hx
  induction h with
  | intro x _ ih =>
    exact Acc.intro _ fun b hb => by
      obtain ⟨y, hy⟩ := b
      refine ih y ?_ hy
      show BH.ltVN y x = true
      simp only [BH.ltVN, hy, Bool.true_and]
      exact hb

/-- Terms of height `≤ n` with at most `n` summands. -/
def bhsUpTo : Nat → List BH.V
  | 0 => []
  | n + 1 =>
      let vs := bhsUpTo n
      let ps := vs.flatMap fun a => [BH.P.D false a, BH.P.D true a]
      (listsOf ps n).map BH.V.node

/-- Atoms of enumeration depth `n`: the normal terms among `bhsUpTo n`. -/
def bachmannHowardUpTo (n : Nat) : List BachmannHoward :=
  (bhsUpTo n).filterMap fun x => if h : BH.nfV x = true then some ⟨x, h⟩ else none

end BusyLean.Ordinal
