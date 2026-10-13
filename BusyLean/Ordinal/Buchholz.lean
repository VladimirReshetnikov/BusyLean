import BusyLean.Ordinal.SortedLexQ
import BusyLean.Ordinal.Epsilon0

/-!
# Atoms below `ψ₀(ε_{Ω_L+1})`: Buchholz-style collapsing with `L+1` levels

Terms are sums of principal terms `D u a` (`ψ_u(a)`), compared lexicographically
(level, then argument), with sums compared lexicographically. Every `D v` term
lies above every `D u` term for `u < v`. A term is normal for the bound `L`
when every level is at most `L`, sums are non-increasing, and `D u a` satisfies
`f < a` for every top-level `u`-component `D u f` of `a` (reached through sums
and higher levels). Buchholz's normal forms satisfy this, so the order type is
at least `ψ₀(ε_{Ω_L+1})`. Over all `L` this reaches `ψ₀(Ω_ω)`.

## Well-foundedness, by downward induction on the level

A *scope* is a predicate `Z` on principal terms; the order is restricted to
normal terms in scope. `stepR` proves, for every level `u ≤ L+1`:

> R(u): if every in-scope term of level `< u` is accessible (in the scoped
> order) and scopes are closed under arguments at levels `≥ u`, then every
> in-scope normal principal term is accessible.

R(L+1) holds because every level is below `L+1`. For R(u), let `Z'` be the
in-scope terms whose top-level `u`-components are accessible.

1. R(u+1) applied to `Z'` makes the order restricted to `Z'` well-founded
   (Claim 1).
2. Induction along it, plus an inner size induction and transitivity, makes
   every `D u a` with `a` accessible within `Z'` accessible (Claim 2).
3. Then every in-scope `D u c` is accessible (Claim 3).
4. Finally R(u+1) applied to `Z` itself gives the conclusion.

R(0) with the full scope gives well-foundedness. The level bound is what stops
the regress: without it, `ψ₀(Ω₉) < Ω₁` would pull arbitrarily high levels into
the argument.
-/

namespace BusyLean.Ordinal

namespace Buch

mutual
/-- Sums `node [p₁, …, p_k]` of principal terms. -/
inductive V where
  | node : List P → V
/-- Principal terms `D u a` (`ψ_u(a)`). -/
inductive P where
  | D : Nat → V → P
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

mutual
def ltV : V → V → Bool
  | .node l, .node m => ltL l m
def ltL : List P → List P → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | p :: l, q :: m => ltP p q || (decide (p = q) && ltL l m)
def ltP : P → P → Bool
  | .D u a, .D v b => decide (u < v) || (decide (u = v) && ltV a b)
end

def P.lev : P → Nat
  | .D u _ => u

mutual
/-- Arguments of the top-level `u`-components (reached through sums and higher levels). -/
def kListV (u : Nat) : V → List V
  | .node l => kListL u l
def kListL (u : Nat) : List P → List V
  | [] => []
  | p :: l => kListP u p ++ kListL u l
def kListP (u : Nat) : P → List V
  | .D v b => if v = u then [b] else if u < v then kListV u b else []
end

mutual
/-- Normal forms for the level bound `L`. -/
def nfV (L : Nat) : V → Bool
  | .node l => sorted ltP l && nfL L l
def nfL (L : Nat) : List P → Bool
  | [] => true
  | p :: l => nfP L p && nfL L l
def nfP (L : Nat) : P → Bool
  | .D u a => decide (u ≤ L) && nfV L a && (kListV u a).all (fun f => ltV f a)
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
      simp only [ltP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
      rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
      · exact Or.inl (Nat.lt_trans h₁ h₂)
      · exact Or.inl h₁
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, ltV_trans a b c h₁ h₂⟩
end

theorem ltL_eq : ∀ l m : List P, ltL l m = Ordinal.llt ltP l m
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: l, q :: m => by simp only [ltL, Ordinal.llt, ltL_eq l m]

/-! ## Scopes -/

/-- A scope, lifted to sums. -/
def ZV (Z : P → Prop) : V → Prop
  | .node l => ∀ q ∈ l, Z q

def QP (L : Nat) (Z : P → Prop) (p : P) : Prop := Z p ∧ nfP L p = true
def QV (L : Nat) (Z : P → Prop) (x : V) : Prop := ZV Z x ∧ nfV L x = true

abbrev AccPZ (L : Nat) (Z : P → Prop) := Acc (LTQ (QP L Z) ltP)
abbrev AccVZ (L : Nat) (Z : P → Prop) := Acc (LTQ (QV L Z) ltV)

variable {L : Nat}

theorem nfP_of_mem : ∀ {m : List P} {q : P}, q ∈ m → nfL L m = true → nfP L q = true
  | _ :: m, q, hq, hn => by
      simp only [nfL, Bool.and_eq_true] at hn
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hn.1
      · exact nfP_of_mem hq hn.2

theorem accPZ_mono {Z Z' : P → Prop} (h : ∀ p, Z' p → Z p) {p : P} (hp : AccPZ L Z p) :
    AccPZ L Z' p :=
  Subrelation.accessible (fun ⟨⟨hz, hn⟩, hl⟩ => ⟨⟨h _ hz, hn⟩, hl⟩) hp

/-- Sums whose summands are accessible as a sorted list are accessible. -/
theorem transferZ (Z : P → Prop) : ∀ l : List P, Acc (SRQ (QP L Z) ltP) l → AccVZ L Z (.node l) := by
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
theorem accVZ_of (Z : P → Prop) (hP : ∀ p, QP L Z p → AccPZ L Z p) :
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
theorem mem_kListV {u : Nat} {Z : P → Prop} (hc : ∀ w b, u ≤ w → Z (.D w b) → ZV Z b) :
    ∀ {c f : V}, f ∈ kListV u c →
      f.size < c.size ∧ (nfV L c = true → nfP L (.D u f) = true) ∧ (ZV Z c → Z (.D u f))
  | .node l, f, h => by
      have := mem_kListL hc (l := l) h
      simp only [V.size, ZV]
      exact ⟨by omega, fun hn => this.2.1 (by simp only [nfV, Bool.and_eq_true] at hn; exact hn.2),
        this.2.2⟩
termination_by c => c.size
decreasing_by all_goals simp only [V.size]; omega

theorem mem_kListL {u : Nat} {Z : P → Prop} (hc : ∀ w b, u ≤ w → Z (.D w b) → ZV Z b) :
    ∀ {l : List P} {f : V}, f ∈ kListL u l →
      f.size < sizeL l ∧ (nfL L l = true → nfP L (.D u f) = true) ∧ ((∀ q ∈ l, Z q) → Z (.D u f))
  | [], f, h => by cases h
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

theorem kListP_sub {u : Nat} : ∀ {m : List P} {q : P} {f : V}, q ∈ m → f ∈ kListP u q → f ∈ kListL u m
  | _ :: m, q, f, hq, hf => by
      simp only [kListL, List.mem_append]
      rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl hf
      · exact Or.inr (kListP_sub hq hf)

/-! ## The level step -/

/-- **R(u) from R(u+1)**, by induction on `n` with `u + n = L + 1`. -/
theorem stepR : ∀ (n u : Nat), u + n = L + 1 → ∀ (Z : P → Prop),
    (∀ w b, u ≤ w → Z (.D w b) → ZV Z b) →
    (∀ p, p.lev < u → QP L Z p → AccPZ L Z p) →
    ∀ p, QP L Z p → AccPZ L Z p := by
  intro n
  induction n with
  | zero =>
    intro u hu Z _ hbase p hp
    apply hbase p _ hp
    match p, hp with
    | .D v a, ⟨_, hn⟩ =>
      simp only [nfP, Bool.and_eq_true, decide_eq_true_eq] at hn
      simp only [P.lev]; omega
  | succ n ihn =>
    intro u hu Z hc hbase
    have hu' : (u + 1) + n = L + 1 := by omega
    -- the restricted scope
    let Z' : P → Prop := fun p => Z p ∧ ∀ f ∈ kListP u p, AccPZ L Z (.D u f)
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
    have hbase' : ∀ p, p.lev < u + 1 → QP L Z' p → AccPZ L Z' p := by
      intro p hl ⟨⟨hz, hk⟩, hn⟩
      by_cases h : p.lev < u
      · exact accPZ_mono (fun _ h => h.1) (hbase p h ⟨hz, hn⟩)
      · match p, hl, h, hk with
        | .D v a, hl, h, hk =>
          simp only [P.lev] at hl h
          have hv : v = u := by omega
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
      have key : ∀ (s : Nat) (c : V), c.size ≤ s → QP L Z (.D u c) → ltV c a = true →
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
                (ltV_trans f _ a (hnc'.2 f hfc) hca)
          exact iha c ⟨⟨hzv', hnc'.1.2⟩, hca⟩ ⟨hzc, hnc⟩
      refine Acc.intro _ fun y ⟨hqy, hy⟩ => ?_
      match y, hqy, hy with
      | .D v c, hqy, hy =>
        simp only [ltP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hy
        rcases hy with hv | ⟨rfl, hca⟩
        · exact hbase _ (by simp only [P.lev]; exact hv) hqy
        · exact key c.size c (Nat.le_refl _) hqy hca
    -- Claim 3: every in-scope `D u c` is accessible
    have claim3 : ∀ (s : Nat) (c : V), c.size ≤ s → QP L Z (.D u c) → AccPZ L Z (.D u c) := by
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
    intro p hl hp
    by_cases h : p.lev < u
    · exact hbase p h hp
    · match p, hl, h, hp with
      | .D v a, hl, h, hp =>
        simp only [P.lev] at hl h
        have hv : v = u := by omega
        subst hv
        exact claim3 a.size a (Nat.le_refl _) hp

def ltPN (L : Nat) (p q : P) : Bool := nfP L p && ltP p q
def ltVN (L : Nat) (x y : V) : Bool := nfV L x && ltV x y

/-- **Every normal principal term is accessible.** -/
theorem accP (p : P) (hp : nfP L p = true) : Acc (LT' (ltPN L)) p := by
  have h := stepR (L + 1) 0 (by omega) (fun _ => True) (fun _ b _ _ => by
      match b with
      | .node l => exact fun _ _ => trivial)
    (fun p h _ => absurd h (Nat.not_lt_zero _)) p ⟨trivial, hp⟩
  exact Subrelation.accessible (fun hr => by
      simp only [LT', ltPN, Bool.and_eq_true] at hr
      exact ⟨⟨trivial, hr.1⟩, hr.2⟩) h

theorem llt_ltPN : ∀ l m : List P, nfL L l = true → Ordinal.llt (ltPN L) l m = Ordinal.llt ltP l m
  | [], [] , _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: l, q :: m, h => by
      simp only [nfL, Bool.and_eq_true] at h
      simp only [Ordinal.llt, ltPN, h.1, Bool.true_and, llt_ltPN l m h.2]

theorem sorted_ltPN : ∀ l : List P, nfL L l = true → sorted ltP l = true → sorted (ltPN L) l = true
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

theorem acc_of_children : ∀ l : List P, Acc (SR (ltPN L)) l → Acc (LT' (ltVN L)) (.node l) := by
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
theorem acc_nf : ∀ x : V, nfV L x = true → Acc (LT' (ltVN L)) x
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
      exact acc_of_children _ (acc_head (accP p hn.2.1) (p :: l)
        (sorted_ltPN _ (by simp only [nfL, Bool.and_eq_true]; exact hn.2) hn.1) rfl)

end Buch

open Buch in
/-- Notations for the ordinals below `ψ₀(ε_{Ω_L+1})`: Buchholz-style terms with levels `≤ L`. -/
def Buchholz (L : Nat) : Type := {x : V // nfV L x = true}

instance (L : Nat) : DecidableEq (Buchholz L) := fun a b =>
  if h : a.1 = b.1 then isTrue (Subtype.ext h) else isFalse (fun e => h (congrArg Subtype.val e))

instance (L : Nat) : FL.AtomOrder (Buchholz L) := ⟨fun a b => Buch.ltV a.1 b.1⟩

theorem buchholz_wf (L : Nat) : WellFounded (FL.ALt (α := Buchholz L)) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨x, hx⟩ := a
  have h := Buch.acc_nf x hx
  induction h with
  | intro x _ ih =>
    exact Acc.intro _ fun b hb => by
      obtain ⟨y, hy⟩ := b
      refine ih y ?_ hy
      show Buch.ltVN L y x = true
      simp only [Buch.ltVN, hy, Bool.true_and]
      exact hb

/-- Terms of height `≤ n`, levels `≤ L`, at most `n` summands. -/
def buchsUpTo (L : Nat) : Nat → List Buch.V
  | 0 => []
  | n + 1 =>
      let vs := buchsUpTo L n
      let ps := vs.flatMap fun a => (List.range (L + 1)).map fun u => Buch.P.D u a
      (listsOf ps n).map Buch.V.node

/-- Atoms of enumeration depth `n` for the level bound `L`. -/
def buchholzUpTo (L n : Nat) : List (Buchholz L) :=
  (buchsUpTo L n).filterMap fun x => if h : Buch.nfV L x = true then some ⟨x, h⟩ else none

end BusyLean.Ordinal
