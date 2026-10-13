import BusyLean.Ordinal.SortedLexQ
import BusyLean.Ordinal.Epsilon0

/-!
# Buchholz-style collapsing over a well-founded base

The notation of `Buchholz.lean`, relativized to a type `β` of *base atoms* with
a transitive, well-founded order. Atoms `B b` lie below every collapse
`D u a`, but may occur inside arguments, so each collapse ranges over
everything below it. `stepR` is unchanged except that atoms are accessible
from the base's well-foundedness (`accB`) instead of from the level induction.

`BaseTower`: the union of all level-bounded systems over a base, ordered by
the level bound first, is again a transitive well-founded order. So it can be
the base of the next round. Iterating gives a tower of notations above
Buchholz's ordinal `ψ₀(Ω_ω)`.
-/

namespace BusyLean.Ordinal

namespace BuchB

variable {β : Type} [DecidableEq β] [FL.AtomOrder β]

/-- The base order is transitive. -/
def BaseTrans (β : Type) [FL.AtomOrder β] : Prop :=
  ∀ a b c : β, FL.AtomOrder.lt a b = true → FL.AtomOrder.lt b c = true → FL.AtomOrder.lt a c = true

/-- The base order is well-founded. -/
def BaseWF (β : Type) [FL.AtomOrder β] : Prop :=
  ∀ b : β, Acc (fun x y : β => FL.AtomOrder.lt x y = true) b

mutual
/-- Sums `node [p₁, …, p_k]` of principal terms. -/
inductive V (β : Type) where
  | node : List (P β) → V β
/-- Principal terms `D u a` (`ψ_u(a)`). -/
inductive P (β : Type) where
  | B : β → P β
  | D : Nat → V β → P β
end

mutual
def decEqV : (x y : (V β)) → Decidable (x = y)
  | .node l, .node m =>
      match decEqL l m with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (V.node.inj e)

def decEqP : (p q : (P β)) → Decidable (p = q)
  | .B a, .B b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (P.B.inj e)
  | .B _, .D _ _ => isFalse fun e => nomatch e
  | .D _ _, .B _ => isFalse fun e => nomatch e
  | .D u a, .D v b =>
      if hu : u = v then
        match decEqV a b with
        | isTrue h => isTrue (hu ▸ h ▸ rfl)
        | isFalse h => isFalse fun e => h (P.D.inj e).2
      else isFalse fun e => hu (P.D.inj e).1

def decEqL : (l m : List (P β)) → Decidable (l = m)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun e => nomatch e
  | _ :: _, [] => isFalse fun e => nomatch e
  | p :: l, q :: m =>
      match decEqP p q, decEqL l m with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse h₁, _ => isFalse fun e => h₁ (List.cons.inj e).1
      | _, isFalse h₂ => isFalse fun e => h₂ (List.cons.inj e).2
end

instance : DecidableEq (V β) := decEqV
instance : DecidableEq (P β) := decEqP

mutual
def ltV : (V β) → (V β) → Bool
  | .node l, .node m => ltL l m
def ltL : List (P β) → List (P β) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | p :: l, q :: m => ltP p q || (decide (p = q) && ltL l m)
def ltP : (P β) → (P β) → Bool
  | .B a, .B b => FL.AtomOrder.lt a b
  | .B _, .D _ _ => true
  | .D _ _, .B _ => false
  | .D u a, .D v b => decide (u < v) || (decide (u = v) && ltV a b)
end

def P.lev : (P β) → Nat
  | .B _ => 0
  | .D u _ => u

mutual
/-- Arguments of the top-level `u`-components (reached through sums and higher levels). -/
def kListV (u : Nat) : (V β) → List (V β)
  | .node l => kListL u l
def kListL (u : Nat) : List (P β) → List (V β)
  | [] => []
  | p :: l => kListP u p ++ kListL u l
def kListP (u : Nat) : (P β) → List (V β)
  | .B _ => []
  | .D v b => if v = u then [b] else if u < v then kListV u b else []
end

mutual
/-- Normal forms for the level bound `L`. -/
def nfV (L : Nat) : (V β) → Bool
  | .node l => sorted ltP l && nfL L l
def nfL (L : Nat) : List (P β) → Bool
  | [] => true
  | p :: l => nfP L p && nfL L l
def nfP (L : Nat) : (P β) → Bool
  | .B _ => true
  | .D u a => decide (u ≤ L) && nfV L a && (kListV u a).all (fun f => ltV f a)
end

mutual
def V.size : (V β) → Nat
  | .node l => 1 + sizeL l
def sizeL : List (P β) → Nat
  | [] => 0
  | p :: l => 1 + p.size + sizeL l
def P.size : (P β) → Nat
  | .B _ => 1
  | .D _ a => 1 + a.size
end

/-! ## Transitivity (structural) -/

mutual
theorem ltV_trans (htr : BaseTrans β) : ∀ x y z : (V β), ltV x y = true → ltV y z = true → ltV x z = true
  | .node l, .node m, .node n, h₁, h₂ => ltL_trans htr l m n h₁ h₂
theorem ltL_trans (htr : BaseTrans β) : ∀ l m n : List (P β), ltL l m = true → ltL m n = true → ltL l n = true
  | [], [], _, h, _ => by simp only [ltL] at h; cases h
  | [], _ :: _, [], _, h => by simp only [ltL] at h; cases h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp only [ltL] at h; cases h
  | _ :: _, _ :: _, [], _, h => by simp only [ltL] at h; cases h
  | p :: l, q :: m, r :: n, h₁, h₂ => by
      simp only [ltL, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
      rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
      · exact Or.inl (ltP_trans htr p q r h₁ h₂)
      · exact Or.inl h₁
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, ltL_trans htr l m n h₁ h₂⟩
theorem ltP_trans (htr : BaseTrans β) : ∀ p q r : (P β), ltP p q = true → ltP q r = true → ltP p r = true
  | .B a, .B b, .B c, h₁, h₂ => htr a b c h₁ h₂
  | .B _, .B _, .D _ _, _, _ => rfl
  | .B _, .D _ _, .D _ _, _, _ => rfl
  | .B _, .D _ _, .B _, _, h => by simp only [ltP] at h; cases h
  | .D _ _, .B _, _, h, _ => by simp only [ltP] at h; cases h
  | .D _ _, .D _ _, .B _, _, h => by simp only [ltP] at h; cases h
  | .D u a, .D v b, .D w c, h₁, h₂ => by
      simp only [ltP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
      rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
      · exact Or.inl (Nat.lt_trans h₁ h₂)
      · exact Or.inl h₁
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, ltV_trans htr a b c h₁ h₂⟩
end

theorem ltL_eq : ∀ l m : List (P β), ltL l m = Ordinal.llt ltP l m
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: l, q :: m => by simp only [ltL, Ordinal.llt, ltL_eq l m]

/-! ## Scopes -/

/-- A scope, lifted to sums. -/
def ZV (Z : (P β) → Prop) : (V β) → Prop
  | .node l => ∀ q ∈ l, Z q

def QP (L : Nat) (Z : (P β) → Prop) (p : (P β)) : Prop := Z p ∧ nfP L p = true
def QV (L : Nat) (Z : (P β) → Prop) (x : (V β)) : Prop := ZV Z x ∧ nfV L x = true

abbrev AccPZ (L : Nat) (Z : (P β) → Prop) := Acc (LTQ (QP L Z) ltP)
abbrev AccVZ (L : Nat) (Z : (P β) → Prop) := Acc (LTQ (QV L Z) ltV)

variable {L : Nat}

theorem nfP_of_mem : ∀ {m : List (P β)} {q : (P β)}, q ∈ m → nfL L m = true → nfP L q = true
  | _ :: m, q, hq, hn => by
      simp only [nfL, Bool.and_eq_true] at hn
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hn.1
      · exact nfP_of_mem hq hn.2

theorem accPZ_mono {Z Z' : (P β) → Prop} (h : ∀ p, Z' p → Z p) {p : (P β)} (hp : AccPZ L Z p) :
    AccPZ L Z' p :=
  Subrelation.accessible (fun ⟨⟨hz, hn⟩, hl⟩ => ⟨⟨h _ hz, hn⟩, hl⟩) hp

/-- Sums whose summands are accessible as a sorted list are accessible. -/
theorem transferZ (Z : (P β) → Prop) : ∀ l : List (P β), Acc (SRQ (QP L Z) ltP) l → AccVZ L Z (.node l) := by
  intro l hl
  induction hl with
  | intro l _ ih =>
    refine Acc.intro _ fun y ⟨⟨hzy, hny⟩, hlt⟩ => ?_
    match y, hzy, hny, hlt with
    | .node m, hzy, hny, hlt =>
      have hn' := hny
      simp only [nfV, Bool.and_eq_true] at hn'
      refine ih m ⟨fun q hq => ⟨hzy q hq, nfP_of_mem hq hn'.2⟩, hn'.1, ?_⟩
      rw [← ltL_eq]; exact hlt

/-- Accessibility of in-scope sums from accessibility of in-scope principal terms. -/
theorem accVZ_of (Z : (P β) → Prop) (hP : ∀ p, QP L Z p → AccPZ L Z p) :
    ∀ x, QV L Z x → AccVZ L Z x
  | .node [], _ => Acc.intro _ fun y ⟨_, h⟩ => by
      match y, h with
      | .node m, h => simp only [ltV, ltL_eq, llt_nil_right] at h; cases h
  | .node (p :: l), ⟨hz, hn⟩ => by
      have hn' := hn
      simp only [nfV, Bool.and_eq_true] at hn'
      have hq : ∀ q ∈ p :: l, QP L Z q := fun q hq => ⟨hz q hq, nfP_of_mem hq hn'.2⟩
      exact transferZ Z _ (accQ_head_of_acc (hP p (hq p List.mem_cons_self))
        (hq p List.mem_cons_self) (p :: l) hq hn'.1 rfl)

/-! ## Components -/

mutual
/-- Top-level `u`-components are smaller, normal, and in scope. -/
theorem mem_kListV {u : Nat} {Z : (P β) → Prop} (hc : ∀ w b, u ≤ w → Z (.D w b) → ZV Z b) :
    ∀ {c f : (V β)}, f ∈ kListV u c →
      f.size < c.size ∧ (nfV L c = true → nfP L (.D u f) = true) ∧ (ZV Z c → Z (.D u f))
  | .node l, f, h => by
      have := mem_kListL hc (l := l) h
      simp only [V.size, ZV]
      exact ⟨by omega, fun hn => this.2.1 (by simp only [nfV, Bool.and_eq_true] at hn; exact hn.2),
        this.2.2⟩
termination_by c => c.size
decreasing_by all_goals simp only [V.size]; omega

theorem mem_kListL {u : Nat} {Z : (P β) → Prop} (hc : ∀ w b, u ≤ w → Z (.D w b) → ZV Z b) :
    ∀ {l : List (P β)} {f : (V β)}, f ∈ kListL u l →
      f.size < sizeL l ∧ (nfL L l = true → nfP L (.D u f) = true) ∧ ((∀ q ∈ l, Z q) → Z (.D u f))
  | [], f, h => by cases h
  | .B _ :: l, f, h => by
      simp only [kListL, kListP, List.nil_append] at h
      have := mem_kListL hc (l := l) h
      refine ⟨by simp only [sizeL]; omega, fun hn => this.2.1 ?_,
        fun hz => this.2.2 (fun q hq => hz q (List.mem_cons_of_mem _ hq))⟩
      simp only [nfL, Bool.and_eq_true] at hn; exact hn.2
  | .D v b :: l, f, h => by
      simp only [kListL, List.mem_append] at h
      rcases h with h | h
      · simp only [kListP] at h
        by_cases hv : v = u
        · subst hv
          simp only [ite_true, List.mem_singleton] at h
          subst h
          refine ⟨by simp only [sizeL, P.size]; omega, fun hn => ?_, fun hz => hz _ List.mem_cons_self⟩
          simp only [nfL, Bool.and_eq_true] at hn; exact hn.1
        · rw [ite_eq_right hv] at h
          by_cases hu : u < v
          · rw [ite_eq_left hu] at h
            have := mem_kListV hc h
            refine ⟨by simp only [sizeL, P.size]; omega, fun hn => this.2.1 ?_,
              fun hz => this.2.2 (hc v b (Nat.le_of_lt hu) (hz _ List.mem_cons_self))⟩
            simp only [nfL, nfP, Bool.and_eq_true] at hn; exact hn.1.1.2
          · rw [ite_eq_right hu] at h; cases h
      · have := mem_kListL hc (l := l) h
        refine ⟨by simp only [sizeL]; omega, fun hn => this.2.1 ?_,
          fun hz => this.2.2 (fun q hq => hz q (List.mem_cons_of_mem _ hq))⟩
        simp only [nfL, Bool.and_eq_true] at hn; exact hn.2
termination_by l => sizeL l
decreasing_by all_goals simp only [sizeL, P.size]; omega
end

omit [DecidableEq β] [FL.AtomOrder β] in
theorem kListP_sub {u : Nat} : ∀ {m : List (P β)} {q : (P β)} {f : (V β)}, q ∈ m → f ∈ kListP u q → f ∈ kListL u m
  | _ :: m, q, f, hq, hf => by
      simp only [kListL, List.mem_append]
      rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl hf
      · exact Or.inr (kListP_sub hq hf)

/-- Base atoms are accessible in every scope. -/
theorem accB (hwf : BaseWF β) {Z : (P β) → Prop} (b : β) : AccPZ L Z (.B b) := by
  induction hwf b with
  | intro b _ ih =>
    refine Acc.intro _ fun y ⟨_, hy⟩ => ?_
    match y, hy with
    | .B c, hy => exact ih c hy
    | .D _ _, hy => simp only [ltP] at hy; cases hy

/-! ## The level step -/

/-- **R(u) from R(u+1)**, by induction on `n` with `u + n = L + 1`. -/
theorem stepR (htr : BaseTrans β) (hwf : BaseWF β) : ∀ (n u : Nat), u + n = L + 1 →
    ∀ (Z : (P β) → Prop),
    (∀ w b, u ≤ w → Z (.D w b) → ZV Z b) →
    (∀ v a, v < u → QP L Z (.D v a) → AccPZ L Z (.D v a)) →
    ∀ p, QP L Z p → AccPZ L Z p := by
  intro n
  induction n with
  | zero =>
    intro u hu Z _ hbase p hp
    match p, hp with
    | .B b, _ => exact accB hwf b
    | .D v a, hp =>
      apply hbase v a _ hp
      have hn := hp.2
      simp only [nfP, Bool.and_eq_true, decide_eq_true_eq] at hn
      omega
  | succ n ihn =>
    intro u hu Z hc hbase
    have hu' : (u + 1) + n = L + 1 := by omega
    -- the restricted scope
    let Z' : (P β) → Prop := fun p => Z p ∧ ∀ f ∈ kListP u p, AccPZ L Z (.D u f)
    have hc' : ∀ w b, u + 1 ≤ w → Z' (.D w b) → ZV Z' b := by
      intro w b hw ⟨hz, hk⟩
      have hzb := hc w b (by omega) hz
      match b, hzb with
      | .node l, hzb =>
        intro q hq
        refine ⟨hzb q hq, fun f hf => hk f ?_⟩
        have hne : w ≠ u := by omega
        have hlt : u < w := by omega
        simp only [kListP, ite_eq_right hne, ite_eq_left hlt, kListV]
        exact kListP_sub hq hf
    have hbase' : ∀ v a, v < u + 1 → QP L Z' (.D v a) → AccPZ L Z' (.D v a) := by
      intro v a hl ⟨⟨hz, hk⟩, hn⟩
      by_cases h : v < u
      · exact accPZ_mono (fun _ h => h.1) (hbase v a h ⟨hz, hn⟩)
      · have hv : v = u := by omega
        subst hv
        exact accPZ_mono (fun _ h => h.1) (hk a (by simp only [kListP, ite_true, List.mem_singleton]))
    -- Claim 1: the order restricted to `Z'` is well-founded
    have claim1 : ∀ x, QV L Z' x → AccVZ L Z' x :=
      accVZ_of Z' (ihn (u + 1) hu' Z' hc' hbase')
    -- Claim 2: `D u a` is accessible when `a` is accessible within `Z'`
    have claim2 : ∀ a, AccVZ L Z' a → QP L Z (.D u a) → AccPZ L Z (.D u a) := by
      intro a ha
      induction ha with
      | intro a _ iha =>
      intro _
      have key : ∀ (s : Nat) (c : (V β)), c.size ≤ s → QP L Z (.D u c) → ltV c a = true →
          AccPZ L Z (.D u c) := by
        intro s
        induction s with
        | zero => intro c hc0; cases c; simp only [V.size] at hc0; exact absurd hc0 (by omega)
        | succ s ihs =>
          intro c hcs ⟨hzc, hnc⟩ hca
          have hnc' := hnc
          simp only [nfP, Bool.and_eq_true, List.all_eq_true] at hnc'
          have hzv : ZV Z c := hc u c (Nat.le_refl u) hzc
          have hzv' : ZV Z' c := by
            match c, hzv with
            | .node l, hzv =>
              intro q hq
              refine ⟨hzv q hq, fun f hf => ?_⟩
              have hfc : f ∈ kListV u (.node l) := by simp only [kListV]; exact kListP_sub hq hf
              obtain ⟨hsz, hnf, hzf⟩ := mem_kListV hc hfc
              exact ihs f (by omega) ⟨hzf hzv, hnf hnc'.1.2⟩
                (ltV_trans htr f _ a (hnc'.2 f hfc) hca)
          exact iha c ⟨⟨hzv', hnc'.1.2⟩, hca⟩ ⟨hzc, hnc⟩
      refine Acc.intro _ fun y ⟨hqy, hy⟩ => ?_
      match y, hqy, hy with
      | .B b, _, _ => exact accB hwf b
      | .D v c, hqy, hy =>
        simp only [ltP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hy
        rcases hy with hv | ⟨rfl, hca⟩
        · exact hbase v c hv hqy
        · exact key c.size c (Nat.le_refl _) hqy hca
    -- Claim 3: every in-scope `D u c` is accessible
    have claim3 : ∀ (s : Nat) (c : (V β)), c.size ≤ s → QP L Z (.D u c) → AccPZ L Z (.D u c) := by
      intro s
      induction s with
      | zero => intro c hc0; cases c; simp only [V.size] at hc0; exact absurd hc0 (by omega)
      | succ s ihs =>
        intro c hcs ⟨hzc, hnc⟩
        have hnc' := hnc
        simp only [nfP, Bool.and_eq_true] at hnc'
        have hzv : ZV Z c := hc u c (Nat.le_refl u) hzc
        have hzv' : ZV Z' c := by
          match c, hzv with
          | .node l, hzv =>
            intro q hq
            refine ⟨hzv q hq, fun f hf => ?_⟩
            have hfc : f ∈ kListV u (.node l) := by simp only [kListV]; exact kListP_sub hq hf
            obtain ⟨hsz, hnf, hzf⟩ := mem_kListV hc hfc
            exact ihs f (by omega) ⟨hzf hzv, hnf hnc'.1.2⟩
        exact claim2 c (claim1 c ⟨hzv', hnc'.1.2⟩) ⟨hzc, hnc⟩
    -- R(u+1) for `Z` itself
    refine ihn (u + 1) hu' Z (fun w b hw hz => hc w b (by omega) hz) ?_
    intro v a hl hp
    by_cases h : v < u
    · exact hbase v a h hp
    · have hv : v = u := by omega
      subst hv
      exact claim3 a.size a (Nat.le_refl _) hp

def ltPN (L : Nat) (p q : (P β)) : Bool := nfP L p && ltP p q
def ltVN (L : Nat) (x y : (V β)) : Bool := nfV L x && ltV x y

/-- **Every normal principal term is accessible.** -/
theorem accP (htr : BaseTrans β) (hwf : BaseWF β) (p : (P β)) (hp : nfP L p = true) :
    Acc (LT' (ltPN L)) p := by
  have h := stepR htr hwf (L + 1) 0 (by omega) (fun _ => True) (fun _ b _ _ => by
      match b with
      | .node l => exact fun _ _ => trivial)
    (fun _ _ h _ => absurd h (Nat.not_lt_zero _)) p ⟨trivial, hp⟩
  exact Subrelation.accessible (fun hr => by
      simp only [LT', ltPN, Bool.and_eq_true] at hr
      exact ⟨⟨trivial, hr.1⟩, hr.2⟩) h

theorem llt_ltPN : ∀ l m : List (P β), nfL L l = true → Ordinal.llt (ltPN L) l m = Ordinal.llt ltP l m
  | [], [] , _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: l, q :: m, h => by
      simp only [nfL, Bool.and_eq_true] at h
      simp only [Ordinal.llt, ltPN, h.1, Bool.true_and, llt_ltPN l m h.2]

theorem sorted_ltPN : ∀ l : List (P β), nfL L l = true → sorted ltP l = true → sorted (ltPN L) l = true
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

theorem acc_of_children : ∀ l : List (P β), Acc (SR (ltPN L)) l → Acc (LT' (ltVN L)) (.node l) := by
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

/-- **Every normal term is accessible.** -/
theorem acc_nf (htr : BaseTrans β) (hwf : BaseWF β) : ∀ x : (V β), nfV L x = true → Acc (LT' (ltVN L)) x
  | .node [], _ => Acc.intro _ fun x hx => by
      match x, hx with
      | .node m, hx =>
        simp only [LT', ltVN, ltV, Bool.and_eq_true] at hx
        have := hx.2
        rw [ltL_eq, llt_nil_right] at this
        cases this
  | .node (p :: l), h => by
      have hn := h
      simp only [nfV, nfL, Bool.and_eq_true] at hn
      exact acc_of_children _ (acc_head (accP htr hwf p hn.2.1) (p :: l)
        (sorted_ltPN _ (by simp only [nfL, Bool.and_eq_true]; exact hn.2) hn.1) rfl)

/-! ## The tower -/

/-- A transitive, well-founded, decidable order with an enumeration. -/
structure WFO where
  T : Type
  dec : DecidableEq T
  lt : T → T → Bool
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  wf : ∀ a, Acc (fun x y => lt x y = true) a
  enum : Nat → List T

instance (W : WFO) : DecidableEq W.T := W.dec
instance (W : WFO) : FL.AtomOrder W.T := ⟨W.lt⟩

def WFO.empty : WFO where
  T := Empty
  dec := fun a => a.elim
  lt := fun a => a.elim
  trans := fun a => a.elim
  wf := fun a => a.elim
  enum := fun _ => []

/-- The union of all level-bounded systems over the base `W`, ordered by the bound first. -/
def sigT (W : WFO) : Type := Σ L : Nat, {x : V W.T // nfV L x = true}

def sigLt (W : WFO) : sigT W → sigT W → Bool
  | ⟨L, x⟩, ⟨L', x'⟩ => decide (L < L') || (decide (L = L') && ltV x.1 x'.1)

def sigDec (W : WFO) : DecidableEq (sigT W)
  | ⟨L, x⟩, ⟨L', x'⟩ =>
      if h : L = L' then by
        subst h
        exact if hx : x.1 = x'.1 then isTrue (by rw [Subtype.ext hx])
          else isFalse fun e => hx (by cases e; rfl)
      else isFalse fun e => h (by cases e; rfl)

theorem sigTrans (W : WFO) : ∀ a b c : sigT W, sigLt W a b = true → sigLt W b c = true →
    sigLt W a c = true
  | ⟨L, x⟩, ⟨M, y⟩, ⟨N, z⟩, h₁, h₂ => by
      simp only [sigLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
      rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
      · exact Or.inl (Nat.lt_trans h₁ h₂)
      · exact Or.inl h₁
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, ltV_trans W.trans x.1 y.1 z.1 h₁ h₂⟩

theorem sigWF (W : WFO) : ∀ (L : Nat) (x : V W.T) (hx : nfV L x = true),
    Acc (fun a b => sigLt W a b = true) (⟨L, ⟨x, hx⟩⟩ : sigT W) := by
  intro L
  induction L using Nat.strongRecOn with
  | ind L ihL =>
    intro x hx
    have h := acc_nf (L := L) W.trans W.wf x hx
    revert hx
    induction h with
    | intro x _ ihx =>
      intro hx
      refine Acc.intro _ fun b hlt => ?_
      obtain ⟨L', y, hy⟩ := b
      simp only [sigLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt
      rcases hlt with hL | ⟨rfl, hyx⟩
      · exact ihL L' hL y hy
      · exact ihx y (by simp only [LT', ltVN, hy, hyx, Bool.and_self]) hy

/-- Terms of height `≤ n`, levels `≤ L`, base atoms from the depth-`n` enumeration. -/
def termsUpTo (W : WFO) (L : Nat) : Nat → List (V W.T)
  | 0 => []
  | n + 1 =>
      let vs := termsUpTo W L n
      let ps := (W.enum n).map P.B ++ vs.flatMap fun a => (List.range (L + 1)).map fun u => P.D u a
      (listsOf ps n).map V.node

def sigEnum (W : WFO) (n : Nat) : List (sigT W) :=
  (List.range (n + 1)).flatMap fun L =>
    (termsUpTo W L n).filterMap fun x => if h : nfV L x = true then some ⟨L, ⟨x, h⟩⟩ else none

/-- The next base: all level-bounded systems over `W`. -/
def WFO.next (W : WFO) : WFO where
  T := sigT W
  dec := sigDec W
  lt := sigLt W
  trans := sigTrans W
  wf := fun ⟨L, x⟩ => sigWF W L x.1 x.2
  enum := sigEnum W

end BuchB

/-- The tower: `tower 1` is the union of the level-bounded Buchholz systems
(order type `ψ₀(Ω_ω)`); each further step collapses over everything below. -/
def tower : Nat → BuchB.WFO
  | 0 => BuchB.WFO.empty
  | k + 1 => (tower k).next

theorem tower_wf (k : Nat) : WellFounded (FL.ALt (α := (tower k).T)) := ⟨(tower k).wf⟩

end BusyLean.Ordinal
