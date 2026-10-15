import BusyLean.SystemFL.Types

/-!
# The ladder with universe levels: syntax, kinding, type-level reduction

The ladder language of `SystemFL`, extended with **level variables**. A
universe atom of a kind is a *level*: a constant atom or a level variable.
Three type formers bind level variables:

* `lall l A`, **bounded quantification** `∀b ≤ l. A`;
* `llam l A`, a **level-indexed operator** `λb ≤ l. A` of kind `lfam l`, a
  family of types indexed by the levels `≤ l`;
* `lapp l F c`, the application of such a family to a level `c ≤ l`.

The bounds are non-strict, as in bounded polymorphism, so every quantifier has
an instance (the bound itself). Packing an operator into the universe `atom a`
still needs its kind to lie *strictly* below `a`; for a level variable this is
read off its bound: `b ≤ l < a`. A level context lists the bounds of the level
variables, innermost first, each relative to the context outside it; `llt`
decides the strict order the context forces.
-/

namespace BusyLean.FLV

open BusyLean.FL (AtomOrder)
open BusyLean.Fw (nth?)
open BusyLean.F.Tm (upRen)

variable {α : Type}

/-! ## Levels -/

inductive Lvl (α : Type) where
  | const : α → Lvl α
  | var : Nat → Lvl α
  deriving DecidableEq

namespace Lvl

def subst (σ : Nat → Lvl α) : Lvl α → Lvl α
  | const a => const a
  | var i => σ i

/-- Renaming, as substitution by variables. -/
abbrev ren (ξ : Nat → Nat) (l : Lvl α) : Lvl α := l.subst fun i => var (ξ i)

def lcons (c : Lvl α) (σ : Nat → Lvl α) : Nat → Lvl α
  | 0 => c
  | i + 1 => σ i

/-- Lift a level substitution under a level binder. -/
def up (σ : Nat → Lvl α) : Nat → Lvl α := lcons (var 0) fun i => (σ i).ren Nat.succ

def eval (η : Nat → α) : Lvl α → α
  | const a => a
  | var i => η i

theorem subst_subst (σ τ : Nat → Lvl α) :
    ∀ l : Lvl α, (l.subst τ).subst σ = l.subst fun i => (τ i).subst σ
  | const _ => rfl
  | var _ => rfl

theorem subst_var : ∀ l : Lvl α, l.subst var = l
  | const _ => rfl
  | var _ => rfl

theorem subst_congr {σ τ : Nat → Lvl α} (h : ∀ i, σ i = τ i) : ∀ l : Lvl α, l.subst σ = l.subst τ
  | const _ => rfl
  | var i => h i

theorem eval_subst (η : Nat → α) (σ : Nat → Lvl α) :
    ∀ l : Lvl α, (l.subst σ).eval η = l.eval fun i => (σ i).eval η
  | const _ => rfl
  | var _ => rfl

/-- `x` with every variable decremented, or `none` for the innermost variable. -/
def unshift? : Lvl α → Option (Lvl α)
  | const a => some (const a)
  | var 0 => none
  | var (i + 1) => some (var i)

theorem unshift?_ren_succ : ∀ l : Lvl α, (l.ren Nat.succ).unshift? = some l
  | const _ => rfl
  | var _ => rfl

theorem unshift?_spec : ∀ {x x' : Lvl α}, x.unshift? = some x' → x = x'.ren Nat.succ
  | const _, _, h => by cases h; rfl
  | var 0, _, h => nomatch h
  | var (_ + 1), _, h => by cases h; rfl

theorem ren_up (σ : Nat → Lvl α) (l : Lvl α) :
    (l.ren Nat.succ).subst (up σ) = (l.subst σ).ren Nat.succ := by
  cases l <;> rfl

end Lvl

/-- A level valuation extended by one level. -/
def lconsA (c : α) (η : Nat → α) : Nat → α
  | 0 => c
  | i + 1 => η i

theorem eval_ren_succ (c : α) (η : Nat → α) (l : Lvl α) :
    (l.ren Nat.succ).eval (lconsA c η) = l.eval η := by
  cases l <;> rfl

/-! ## The order forced by a level context -/

section Order

variable [AtomOrder α]

/-- The order of two constant levels (nothing is known about a variable). -/
def lltC : Lvl α → Lvl α → Bool
  | .const b, .const a => AtomOrder.lt b a
  | _, _ => false

/-- `llt Λ c x`: the bounds `Λ` force `c < x`. A variable lies at or below its
bound, so `var i < x` follows from `bound i < x`. -/
def llt : List (Lvl α) → Lvl α → Lvl α → Bool
  | [], c, x => lltC c x
  | l :: Λ, c, x =>
      match c with
      | .const _ => lltC c x
      | .var 0 =>
          match x.unshift? with
          | some x' => llt Λ l x'
          | none => false
      | .var (i + 1) =>
          match x.unshift? with
          | some x' => llt Λ (.var i) x'
          | none => false

/-- `lle Λ c x`: `c = x` or the bounds force `c < x`. -/
def lle [DecidableEq α] (Λ : List (Lvl α)) (c x : Lvl α) : Bool := decide (c = x) || llt Λ c x

/-- `c ≤ a` in the atom order. -/
def LeA (c a : α) : Prop := c = a ∨ AtomOrder.lt c a = true

/-- A level valuation respects the bounds of a level context. -/
def LGood : List (Lvl α) → (Nat → α) → Prop
  | [], _ => True
  | l :: Λ, η => LeA (η 0) (l.eval fun i => η (i + 1)) ∧ LGood Λ fun i => η (i + 1)

/-- The atom order is transitive. -/
def LtTrans (α : Type) [AtomOrder α] : Prop :=
  ∀ a b c : α, AtomOrder.lt a b = true → AtomOrder.lt b c = true → AtomOrder.lt a c = true

omit [AtomOrder α] in
theorem Lvl.unshift?_none : ∀ {x : Lvl α}, x.unshift? = none → x = .var 0
  | .const _, h => nomatch h
  | .var 0, _ => rfl
  | .var (_ + 1), h => nomatch h

theorem llt_const_left (Λ : List (Lvl α)) (b : α) (x : Lvl α) :
    llt Λ (.const b) x = lltC (.const b) x := by
  cases Λ <;> rfl

theorem lltC_var (c : Lvl α) (j : Nat) : lltC c (.var j) = false := by
  cases c <;> rfl

theorem llt_false_var0 (Λ : List (Lvl α)) (c : Lvl α) : llt Λ c (.var 0) = false := by
  cases Λ with
  | nil => exact lltC_var c 0
  | cons l Λ =>
      cases c with
      | const b => exact lltC_var (.const b) 0
      | var i => cases i <;> rfl

/-- Shifting both sides under a new level variable does not change the forced order. -/
theorem llt_cons_ren (l : Lvl α) (Λ : List (Lvl α)) (b c : Lvl α) :
    llt (l :: Λ) (b.ren Nat.succ) (c.ren Nat.succ) = llt Λ b c := by
  cases b with
  | const b' =>
      rw [llt_const_left]
      show lltC (.const b') (c.ren Nat.succ) = lltC (.const b') c
      cases c <;> rfl
  | var j =>
      show llt (l :: Λ) (.var (j + 1)) (c.ren Nat.succ) = _
      simp only [llt, Lvl.unshift?_ren_succ]

omit [AtomOrder α] in
theorem eval_unshift {x x' : Lvl α} (h : x.unshift? = some x') (η : Nat → α) :
    x.eval η = x'.eval fun i => η (i + 1) := by
  rw [Lvl.unshift?_spec h]
  cases x' <;> rfl

theorem lltC_sound {c x : Lvl α} (η : Nat → α) (h : lltC c x = true) :
    AtomOrder.lt (c.eval η) (x.eval η) = true := by
  cases c with
  | const b =>
      cases x with
      | const a => exact h
      | var _ => exact absurd h (by simp [lltC])
  | var _ => exact absurd h (by simp [lltC])

/-- **Soundness of the forced order.** -/
theorem llt_sound (htr : LtTrans α) (Λ : List (Lvl α)) : ∀ (η : Nat → α) (c x : Lvl α),
    LGood Λ η → llt Λ c x = true → AtomOrder.lt (c.eval η) (x.eval η) = true := by
  induction Λ with
  | nil => intro η c x _ h; exact lltC_sound η h
  | cons l Λ ih =>
      intro η c x hg h
      cases c with
      | const b => exact lltC_sound η h
      | var i =>
          cases hx : x.unshift? with
          | none => rw [Lvl.unshift?_none hx, llt_false_var0] at h; cases h
          | some x' =>
              rw [eval_unshift hx]
              cases i with
              | zero =>
                  simp only [llt, hx] at h
                  have h1 := ih _ l x' hg.2 h
                  rcases hg.1 with e | e
                  · show AtomOrder.lt (η 0) _ = true
                    rw [e]; exact h1
                  · exact htr _ _ _ e h1
              | succ i =>
                  simp only [llt, hx] at h
                  exact ih _ (.var i) x' hg.2 h

theorem lle_sound [DecidableEq α] (htr : LtTrans α) {Λ : List (Lvl α)} {η : Nat → α} {c x : Lvl α}
    (hg : LGood Λ η) (h : lle Λ c x = true) : LeA (c.eval η) (x.eval η) := by
  unfold lle at h
  rcases Bool.or_eq_true_iff.1 h with e | e
  · left; rw [of_decide_eq_true e]
  · exact Or.inr (llt_sound htr Λ η c x hg e)

/-- Weakening: the order survives an extra level variable. -/
theorem llt_weaken (l : Lvl α) {Λ : List (Lvl α)} {c x : Lvl α} (h : llt Λ c x = true) :
    llt (l :: Λ) (c.ren Nat.succ) (x.ren Nat.succ) = true := by
  rw [llt_cons_ren]; exact h

theorem lltC_trans (htr : LtTrans α) {a b c : Lvl α} (h1 : lltC a b = true) (h2 : lltC b c = true) :
    lltC a c = true := by
  cases a with
  | var _ => exact absurd h1 (by simp [lltC])
  | const a' =>
      cases b with
      | var _ => exact absurd h1 (by simp [lltC])
      | const b' =>
          cases c with
          | var _ => exact absurd h2 (by simp [lltC])
          | const c' => exact htr _ _ _ h1 h2

/-- The forced order is transitive. -/
theorem llt_trans (htr : LtTrans α) (Λ : List (Lvl α)) : ∀ {a b c : Lvl α},
    llt Λ a b = true → llt Λ b c = true → llt Λ a c = true := by
  induction Λ with
  | nil => intro a b c h1 h2; exact lltC_trans htr h1 h2
  | cons l Λ ih =>
      intro a b c h1 h2
      cases a with
      | const a' =>
          rw [llt_const_left] at h1 ⊢
          cases b with
          | var _ => exact absurd h1 (by simp [lltC])
          | const b' =>
              rw [llt_const_left] at h2
              exact lltC_trans htr h1 h2
      | var j =>
          cases hb : b.unshift? with
          | none => rw [Lvl.unshift?_none hb, llt_false_var0] at h1; cases h1
          | some b' =>
              cases hc : c.unshift? with
              | none => rw [Lvl.unshift?_none hc, llt_false_var0] at h2; cases h2
              | some c' =>
                  have h2' : llt Λ b' c' = true := by
                    rw [Lvl.unshift?_spec hb, Lvl.unshift?_spec hc, llt_cons_ren] at h2
                    exact h2
                  cases j with
                  | zero =>
                      simp only [llt, hb] at h1
                      simp only [llt, hc]
                      exact ih h1 h2'
                  | succ i =>
                      simp only [llt, hb] at h1
                      simp only [llt, hc]
                      exact ih h1 h2'

/-- A level substitution that respects the forced order. -/
def LMap (Λ Λ' : List (Lvl α)) (σ : Nat → Lvl α) : Prop :=
  ∀ c x : Lvl α, llt Λ c x = true → llt Λ' (c.subst σ) (x.subst σ) = true

theorem LMap.weaken (l : Lvl α) (Λ : List (Lvl α)) :
    LMap Λ (l :: Λ) fun i => .var (i + 1) := fun _ _ h => llt_weaken l h

theorem LMap.up {Λ Λ' : List (Lvl α)} {σ : Nat → Lvl α} (h : LMap Λ Λ' σ) (l : Lvl α) :
    LMap (l :: Λ) (l.subst σ :: Λ') (Lvl.up σ) := by
  intro c x hcx
  cases hx : x.unshift? with
  | none => rw [Lvl.unshift?_none hx, llt_false_var0] at hcx; cases hcx
  | some x' =>
      have ex : x = x'.ren Nat.succ := Lvl.unshift?_spec hx
      have ex' : x.subst (Lvl.up σ) = (x'.subst σ).ren Nat.succ := by
        rw [ex]; exact Lvl.ren_up σ x'
      rw [ex']
      cases c with
      | const b =>
          rw [ex, llt_const_left] at hcx
          rw [show (Lvl.const b).subst (Lvl.up σ) = Lvl.const b from rfl, llt_const_left]
          cases x' with
          | const a => exact hcx
          | var _ => exact absurd hcx (by show ¬(false = true); decide)
      | var i =>
          cases i with
          | zero =>
              simp only [llt, hx] at hcx
              show llt (l.subst σ :: Λ') (.var 0) ((x'.subst σ).ren Nat.succ) = true
              simp only [llt, Lvl.unshift?_ren_succ]
              exact h l x' hcx
          | succ i =>
              simp only [llt, hx] at hcx
              show llt (l.subst σ :: Λ') ((σ i).ren Nat.succ) ((x'.subst σ).ren Nat.succ) = true
              exact llt_weaken _ (h (.var i) x' hcx)

/-- Instantiating the innermost level variable at a level `c ≤ l`. -/
theorem LMap.inst [DecidableEq α] (htr : LtTrans α) {Λ : List (Lvl α)} {l c : Lvl α}
    (hc : lle Λ c l = true) : LMap (l :: Λ) Λ (Lvl.lcons c Lvl.var) := by
  intro d x hdx
  cases hx : x.unshift? with
  | none => rw [Lvl.unshift?_none hx, llt_false_var0] at hdx; cases hdx
  | some x' =>
      have ex : x.subst (Lvl.lcons c Lvl.var) = x' := by
        rw [Lvl.unshift?_spec hx]
        cases x' <;> rfl
      rw [ex]
      cases d with
      | const b =>
          rw [llt_const_left, Lvl.unshift?_spec hx] at hdx
          rw [show (Lvl.const b).subst (Lvl.lcons c Lvl.var) = Lvl.const b from rfl, llt_const_left]
          cases x' with
          | const a => exact hdx
          | var _ => exact absurd hdx (by show ¬(false = true); decide)
      | var i =>
          cases i with
          | zero =>
              simp only [llt, hx] at hdx
              show llt Λ c x' = true
              unfold lle at hc
              rcases Bool.or_eq_true_iff.1 hc with e | e
              · rw [of_decide_eq_true e]; exact hdx
              · exact llt_trans htr Λ e hdx
          | succ i =>
              simp only [llt, hx] at hdx
              exact hdx

theorem LMap.lle_pres [DecidableEq α] {Λ Λ' : List (Lvl α)} {σ : Nat → Lvl α} (h : LMap Λ Λ' σ)
    {c x : Lvl α} (hcx : lle Λ c x = true) : lle Λ' (c.subst σ) (x.subst σ) = true := by
  unfold lle at hcx ⊢
  rcases Bool.or_eq_true_iff.1 hcx with e | e
  · rw [of_decide_eq_true e]; simp
  · exact Bool.or_eq_true_iff.2 (Or.inr (h c x e))

end Order

/-! ## Kinds -/

/-- Kinds: those of `SystemFL`, where an atom is a *level*, plus the kind
`lfam l k` of level-indexed operators, which take every level `≤ l` to an
operator of kind `k`. -/
inductive Kind (α : Type) where
  | star : Kind α
  | arr : Kind α → Kind α → Kind α
  | kvar : Nat → Kind α
  | dvar : Nat → Kind α
  | dyn : Kind α
  | atom : Lvl α → Kind α
  | lfam : Lvl α → Kind α → Kind α
  deriving DecidableEq

namespace Kind

/-- Rename level-0 and level-1 kind variables. -/
def ren (ξ₀ ξ₁ : Nat → Nat) : Kind α → Kind α
  | star => star
  | arr a b => arr (ren ξ₀ ξ₁ a) (ren ξ₀ ξ₁ b)
  | kvar n => kvar (ξ₀ n)
  | dvar n => dvar (ξ₁ n)
  | dyn => dyn
  | atom l => atom l
  | lfam l k => lfam l (ren ξ₀ ξ₁ k)

/-- Substitute for level-0 and level-1 kind variables. -/
def subst (σ₀ σ₁ : Nat → Kind α) : Kind α → Kind α
  | star => star
  | arr a b => arr (subst σ₀ σ₁ a) (subst σ₀ σ₁ b)
  | kvar n => σ₀ n
  | dvar n => σ₁ n
  | dyn => dyn
  | atom l => atom l
  | lfam l k => lfam l (subst σ₀ σ₁ k)

/-- Substitute for level variables. -/
def lsubst (σ : Nat → Lvl α) : Kind α → Kind α
  | star => star
  | arr a b => arr (lsubst σ a) (lsubst σ b)
  | kvar n => kvar n
  | dvar n => dvar n
  | dyn => dyn
  | atom l => atom (l.subst σ)
  | lfam l k => lfam (l.subst σ) (lsubst σ k)

/-- Shift the level variables, to enter a level binder. -/
abbrev lsh (K : Kind α) : Kind α := K.lsubst fun i => .var (i + 1)

/-- Evaluate the levels under a valuation. -/
def leval (η : Nat → α) : Kind α → Kind α
  | star => star
  | arr a b => arr (leval η a) (leval η b)
  | kvar n => kvar n
  | dvar n => dvar n
  | dyn => dyn
  | atom l => atom (.const (l.eval η))
  | lfam l k => lfam (.const (l.eval η)) (leval η k)

def kcons (K : Kind α) (σ : Nat → Kind α) : Nat → Kind α
  | 0 => K
  | n + 1 => σ n

/-- Dyn-free kinds: no `dyn`, no level-1 variable, no level family. -/
def DynFree : Kind α → Prop
  | star => True
  | arr a b => DynFree a ∧ DynFree b
  | kvar _ => True
  | dvar _ => False
  | dyn => False
  | atom _ => True
  | lfam _ _ => False

def dynFree : Kind α → Bool
  | star => true
  | arr a b => dynFree a && dynFree b
  | kvar _ => true
  | dvar _ => false
  | dyn => false
  | atom _ => true
  | lfam _ _ => false

theorem dynFree_iff : ∀ K : Kind α, dynFree K = true ↔ DynFree K
  | star => by simp [dynFree, DynFree]
  | arr a b => by simp [dynFree, DynFree, dynFree_iff a, dynFree_iff b]
  | kvar _ => by simp [dynFree, DynFree]
  | dvar _ => by simp [dynFree, DynFree]
  | dyn => by simp [dynFree, DynFree]
  | atom _ => by simp [dynFree, DynFree]
  | lfam _ _ => by simp [dynFree, DynFree]

theorem ren_ren : ∀ (K : Kind α) (ξ₀ ξ₁ ζ₀ ζ₁ : Nat → Nat),
    ren ξ₀ ξ₁ (ren ζ₀ ζ₁ K) = ren (ξ₀ ∘ ζ₀) (ξ₁ ∘ ζ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, ren_ren a, ren_ren b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl
  | atom _, _, _, _, _ => rfl
  | lfam _ k, _, _, _, _ => by simp only [ren, ren_ren k]

theorem subst_ren : ∀ (K : Kind α) (σ₀ σ₁ : Nat → Kind α) (ξ₀ ξ₁ : Nat → Nat),
    subst σ₀ σ₁ (ren ξ₀ ξ₁ K) = subst (σ₀ ∘ ξ₀) (σ₁ ∘ ξ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, subst, subst_ren a, subst_ren b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl
  | atom _, _, _, _, _ => rfl
  | lfam _ k, _, _, _, _ => by simp only [ren, subst, subst_ren k]

theorem ren_subst : ∀ (K : Kind α) (σ₀ σ₁ : Nat → Kind α) (ξ₀ ξ₁ : Nat → Nat),
    ren ξ₀ ξ₁ (subst σ₀ σ₁ K) = subst (ren ξ₀ ξ₁ ∘ σ₀) (ren ξ₀ ξ₁ ∘ σ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, subst, ren_subst a, ren_subst b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl
  | atom _, _, _, _, _ => rfl
  | lfam _ k, _, _, _, _ => by simp only [ren, subst, ren_subst k]

theorem subst_subst : ∀ (K : Kind α) (σ₀ σ₁ τ₀ τ₁ : Nat → Kind α),
    subst σ₀ σ₁ (subst τ₀ τ₁ K) = subst (subst σ₀ σ₁ ∘ τ₀) (subst σ₀ σ₁ ∘ τ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [subst, subst_subst a, subst_subst b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl
  | atom _, _, _, _, _ => rfl
  | lfam _ k, _, _, _, _ => by simp only [subst, subst_subst k]

theorem subst_var : ∀ K : Kind α, subst kvar dvar K = K
  | star => rfl
  | arr a b => by simp only [subst, subst_var a, subst_var b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom _ => rfl
  | lfam _ k => by simp only [subst, subst_var k]

theorem lsubst_lsubst (σ τ : Nat → Lvl α) : ∀ K : Kind α,
    (K.lsubst τ).lsubst σ = K.lsubst fun i => (τ i).subst σ
  | star => rfl
  | arr a b => by simp only [lsubst, lsubst_lsubst σ τ a, lsubst_lsubst σ τ b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom l => by simp only [lsubst, Lvl.subst_subst]
  | lfam l k => by simp only [lsubst, Lvl.subst_subst, lsubst_lsubst σ τ k]

theorem lsubst_congr {σ τ : Nat → Lvl α} (h : ∀ i, σ i = τ i) :
    ∀ K : Kind α, K.lsubst σ = K.lsubst τ
  | star => rfl
  | arr a b => by simp only [lsubst, lsubst_congr h a, lsubst_congr h b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom l => by simp only [lsubst, Lvl.subst_congr h l]
  | lfam l k => by simp only [lsubst, Lvl.subst_congr h l, lsubst_congr h k]

theorem lsubst_var : ∀ K : Kind α, K.lsubst Lvl.var = K
  | star => rfl
  | arr a b => by simp only [lsubst, lsubst_var a, lsubst_var b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom l => by simp only [lsubst, Lvl.subst_var]
  | lfam l k => by simp only [lsubst, Lvl.subst_var, lsubst_var k]

/-- Kind variables and levels do not interact. -/
theorem ren_lsubst (σ : Nat → Lvl α) (ξ₀ ξ₁ : Nat → Nat) : ∀ K : Kind α,
    (K.lsubst σ).ren ξ₀ ξ₁ = (K.ren ξ₀ ξ₁).lsubst σ
  | star => rfl
  | arr a b => by simp only [lsubst, ren, ren_lsubst σ ξ₀ ξ₁ a, ren_lsubst σ ξ₀ ξ₁ b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom _ => rfl
  | lfam _ k => by simp only [lsubst, ren, ren_lsubst σ ξ₀ ξ₁ k]

theorem subst_lsubst (τ : Nat → Lvl α) (σ₀ σ₁ : Nat → Kind α) : ∀ K : Kind α,
    (K.subst σ₀ σ₁).lsubst τ =
      (K.lsubst τ).subst (fun n => (σ₀ n).lsubst τ) (fun n => (σ₁ n).lsubst τ)
  | star => rfl
  | arr a b => by simp only [lsubst, subst, subst_lsubst τ σ₀ σ₁ a, subst_lsubst τ σ₀ σ₁ b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom _ => rfl
  | lfam _ k => by simp only [lsubst, subst, subst_lsubst τ σ₀ σ₁ k]

theorem lsh_lsubst_up (σ : Nat → Lvl α) (K : Kind α) :
    K.lsh.lsubst (Lvl.up σ) = (K.lsubst σ).lsh := by
  show (K.lsubst _).lsubst (Lvl.up σ) = (K.lsubst σ).lsubst _
  rw [lsubst_lsubst, lsubst_lsubst]
  exact lsubst_congr (fun _ => rfl) K

theorem lsh_lsubst_lcons (c : Lvl α) (K : Kind α) : K.lsh.lsubst (Lvl.lcons c Lvl.var) = K := by
  rw [lsubst_lsubst]
  exact (lsubst_congr (fun _ => rfl) K).trans (lsubst_var K)

theorem leval_lsubst (η : Nat → α) (σ : Nat → Lvl α) : ∀ K : Kind α,
    (K.lsubst σ).leval η = K.leval fun i => (σ i).eval η
  | star => rfl
  | arr a b => by simp only [lsubst, leval, leval_lsubst η σ a, leval_lsubst η σ b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom l => by simp only [lsubst, leval, Lvl.eval_subst]
  | lfam l k => by simp only [lsubst, leval, Lvl.eval_subst, leval_lsubst η σ k]

theorem leval_ren (η : Nat → α) (ξ₀ ξ₁ : Nat → Nat) : ∀ K : Kind α,
    (K.ren ξ₀ ξ₁).leval η = (K.leval η).ren ξ₀ ξ₁
  | star => rfl
  | arr a b => by simp only [ren, leval, leval_ren η ξ₀ ξ₁ a, leval_ren η ξ₀ ξ₁ b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom _ => rfl
  | lfam _ k => by simp only [ren, leval, leval_ren η ξ₀ ξ₁ k]

theorem leval_subst (η : Nat → α) (σ₀ σ₁ : Nat → Kind α) : ∀ K : Kind α,
    (K.subst σ₀ σ₁).leval η =
      (K.leval η).subst (fun n => (σ₀ n).leval η) (fun n => (σ₁ n).leval η)
  | star => rfl
  | arr a b => by simp only [subst, leval, leval_subst η σ₀ σ₁ a, leval_subst η σ₀ σ₁ b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom _ => rfl
  | lfam _ k => by simp only [subst, leval, leval_subst η σ₀ σ₁ k]

theorem leval_lsh (c : α) (η : Nat → α) (K : Kind α) : K.lsh.leval (lconsA c η) = K.leval η := by
  rw [leval_lsubst]
  rfl

theorem DynFree.ren {K : Kind α} (h : DynFree K) (ξ₀ ξ₁ : Nat → Nat) : DynFree (ren ξ₀ ξ₁ K) := by
  induction K with
  | star => trivial
  | arr a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | kvar _ => trivial
  | dvar _ => exact h.elim
  | dyn => exact h.elim
  | atom _ => trivial
  | lfam _ _ _ => exact h.elim

theorem DynFree.subst {K : Kind α} (h : DynFree K) {σ₀ σ₁ : Nat → Kind α}
    (hσ : ∀ n, DynFree (σ₀ n)) : DynFree (subst σ₀ σ₁ K) := by
  induction K with
  | star => trivial
  | arr a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | kvar n => exact hσ n
  | dvar _ => exact h.elim
  | dyn => exact h.elim
  | atom _ => trivial
  | lfam _ _ _ => exact h.elim

theorem DynFree.lsubst {K : Kind α} (h : DynFree K) (σ : Nat → Lvl α) : DynFree (K.lsubst σ) := by
  induction K with
  | star => trivial
  | arr a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | kvar _ => trivial
  | dvar _ => exact h.elim
  | dyn => exact h.elim
  | atom _ => trivial
  | lfam _ _ _ => exact h.elim

/-- Strip one level shift, if level variable `0` does not occur. -/
def unshift? : Kind α → Option (Kind α)
  | star => some star
  | arr a b =>
      match unshift? a, unshift? b with
      | some a', some b' => some (arr a' b')
      | _, _ => none
  | kvar n => some (kvar n)
  | dvar n => some (dvar n)
  | dyn => some dyn
  | atom l =>
      match l.unshift? with
      | some l' => some (atom l')
      | none => none
  | lfam l k =>
      match l.unshift?, unshift? k with
      | some l', some k' => some (lfam l' k')
      | _, _ => none

theorem unshift?_spec : ∀ {K K' : Kind α}, K.unshift? = some K' → K = K'.lsh
  | star, _, h => by cases h; rfl
  | arr a b, _, h => by
      unfold unshift? at h
      split at h
      · next a' b' ha hb =>
          cases h
          rw [unshift?_spec ha, unshift?_spec hb]
          rfl
      · cases h
  | kvar _, _, h => by cases h; rfl
  | dvar _, _, h => by cases h; rfl
  | dyn, _, h => by cases h; rfl
  | atom l, _, h => by
      unfold unshift? at h
      split at h
      · next l' hl =>
          cases h
          rw [Lvl.unshift?_spec hl]
          rfl
      · cases h
  | lfam l k, _, h => by
      unfold unshift? at h
      split at h
      · next l' k' hl hk =>
          cases h
          rw [Lvl.unshift?_spec hl, unshift?_spec hk]
          rfl
      · cases h

section Fits

variable [AtomOrder α]

/-- `K` is a closed base kind (no kind variable, `dyn` or level family) whose
atoms the level context `Λ` forces strictly below `l`: the kinds whose
operators can be packed into the atom `l`. -/
def Fits (Λ : List (Lvl α)) (l : Lvl α) : Kind α → Prop
  | star => True
  | arr x y => Fits Λ l x ∧ Fits Λ l y
  | atom b => llt Λ b l = true
  | kvar _ => False
  | dvar _ => False
  | dyn => False
  | lfam _ _ => False

def fits (Λ : List (Lvl α)) (l : Lvl α) : Kind α → Bool
  | star => true
  | arr x y => fits Λ l x && fits Λ l y
  | atom b => llt Λ b l
  | kvar _ => false
  | dvar _ => false
  | dyn => false
  | lfam _ _ => false

theorem fits_iff (Λ : List (Lvl α)) (l : Lvl α) : ∀ K : Kind α, fits Λ l K = true ↔ Fits Λ l K
  | star => by simp [fits, Fits]
  | arr x y => by simp [fits, Fits, fits_iff Λ l x, fits_iff Λ l y]
  | atom _ => by simp [fits, Fits]
  | kvar _ => by simp [fits, Fits]
  | dvar _ => by simp [fits, Fits]
  | dyn => by simp [fits, Fits]
  | lfam _ _ => by simp [fits, Fits]

/-- Fitting kinds have no kind variables, hence are fixed by renaming and substitution. -/
theorem Fits.ren_eq {Λ : List (Lvl α)} {l : Lvl α} {K : Kind α} (h : Fits Λ l K)
    (ξ₀ ξ₁ : Nat → Nat) : ren ξ₀ ξ₁ K = K := by
  induction K with
  | star => rfl
  | arr x y ihx ihy => simp only [ren, ihx h.1, ihy h.2]
  | atom _ => rfl
  | kvar _ => exact h.elim
  | dvar _ => exact h.elim
  | dyn => exact h.elim
  | lfam _ _ _ => exact h.elim

theorem Fits.subst_eq {Λ : List (Lvl α)} {l : Lvl α} {K : Kind α} (h : Fits Λ l K)
    (σ₀ σ₁ : Nat → Kind α) : subst σ₀ σ₁ K = K := by
  induction K with
  | star => rfl
  | arr x y ihx ihy => simp only [subst, ihx h.1, ihy h.2]
  | atom _ => rfl
  | kvar _ => exact h.elim
  | dvar _ => exact h.elim
  | dyn => exact h.elim
  | lfam _ _ _ => exact h.elim

theorem Fits.lsubst {Λ Λ' : List (Lvl α)} {σ : Nat → Lvl α} (hσ : LMap Λ Λ' σ) {l : Lvl α}
    {K : Kind α} (h : Fits Λ l K) : Fits Λ' (l.subst σ) (K.lsubst σ) := by
  induction K with
  | star => trivial
  | arr x y ihx ihy => exact ⟨ihx h.1, ihy h.2⟩
  | atom b => exact hσ b l h
  | kvar _ => exact h.elim
  | dvar _ => exact h.elim
  | dyn => exact h.elim
  | lfam _ _ _ => exact h.elim

end Fits

/-- Shifts for entering a level-0 / level-1 kind binder. -/
def sh₀ (K : Kind α) : Kind α := ren Nat.succ id K
def sh₁ (K : Kind α) : Kind α := ren id Nat.succ K

end Kind

/-! ## Types -/

inductive Ty (α : Type) where
  | tvar : Nat → Ty α
  | arr : Ty α → Ty α → Ty α
  | all : Kind α → Ty α → Ty α
  | lam : Kind α → Ty α → Ty α
  | app : Kind α → Ty α → Ty α → Ty α
  | kall0 : Ty α → Ty α
  | kall1 : Ty α → Ty α
  | pack : Kind α → Ty α → Ty α
  | unpack : Kind α → Ty α → Ty α
  | apack : Lvl α → Kind α → Ty α → Ty α
  | aunpack : Lvl α → Kind α → Ty α → Ty α
  /-- Bounded quantification `∀b ≤ l. A`. -/
  | lall : Lvl α → Ty α → Ty α
  /-- A level-indexed operator `λb ≤ l. A`. -/
  | llam : Lvl α → Ty α → Ty α
  /-- `lapp l F c`: the operator `F`, indexed by the levels `≤ l`, at level `c`. -/
  | lapp : Lvl α → Ty α → Lvl α → Ty α
  deriving DecidableEq

namespace Ty

def tren (ξ : Nat → Nat) : Ty α → Ty α
  | tvar n => tvar (ξ n)
  | arr A B => arr (tren ξ A) (tren ξ B)
  | all k A => all k (tren (upRen ξ) A)
  | lam k A => lam k (tren (upRen ξ) A)
  | app k A B => app k (tren ξ A) (tren ξ B)
  | kall0 A => kall0 (tren ξ A)
  | kall1 A => kall1 (tren ξ A)
  | pack k A => pack k (tren ξ A)
  | unpack k A => unpack k (tren ξ A)
  | apack l k A => apack l k (tren ξ A)
  | aunpack l k A => aunpack l k (tren ξ A)
  | lall l A => lall l (tren ξ A)
  | llam l A => llam l (tren ξ A)
  | lapp l A c => lapp l (tren ξ A) c

/-- Rename kind variables of both levels. -/
def kren (ξ₀ ξ₁ : Nat → Nat) : Ty α → Ty α
  | tvar n => tvar n
  | arr A B => arr (kren ξ₀ ξ₁ A) (kren ξ₀ ξ₁ B)
  | all k A => all (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | lam k A => lam (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | app k A B => app (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A) (kren ξ₀ ξ₁ B)
  | kall0 A => kall0 (kren (upRen ξ₀) ξ₁ A)
  | kall1 A => kall1 (kren ξ₀ (upRen ξ₁) A)
  | pack k A => pack (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | unpack k A => unpack (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | apack l k A => apack l (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | aunpack l k A => aunpack l (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | lall l A => lall l (kren ξ₀ ξ₁ A)
  | llam l A => llam l (kren ξ₀ ξ₁ A)
  | lapp l A c => lapp l (kren ξ₀ ξ₁ A) c

/-- Lift kind substitutions under a level-0 binder. -/
def kup₀ (σ₀ σ₁ : Nat → Kind α) : (Nat → Kind α) × (Nat → Kind α) :=
  (Kind.kcons (.kvar 0) (fun n => (σ₀ n).sh₀), fun n => (σ₁ n).sh₀)

/-- Lift kind substitutions under a level-1 binder. -/
def kup₁ (σ₀ σ₁ : Nat → Kind α) : (Nat → Kind α) × (Nat → Kind α) :=
  (fun n => (σ₀ n).sh₁, Kind.kcons (.dvar 0) (fun n => (σ₁ n).sh₁))

/-- Substitute for kind variables; the substituted kinds are shifted under level binders. -/
def ksubst (σ₀ σ₁ : Nat → Kind α) : Ty α → Ty α
  | tvar n => tvar n
  | arr A B => arr (ksubst σ₀ σ₁ A) (ksubst σ₀ σ₁ B)
  | all k A => all (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | lam k A => lam (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | app k A B => app (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A) (ksubst σ₀ σ₁ B)
  | kall0 A => kall0 (ksubst (kup₀ σ₀ σ₁).1 (kup₀ σ₀ σ₁).2 A)
  | kall1 A => kall1 (ksubst (kup₁ σ₀ σ₁).1 (kup₁ σ₀ σ₁).2 A)
  | pack k A => pack (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | unpack k A => unpack (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | apack l k A => apack l (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | aunpack l k A => aunpack l (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | lall l A => lall l (ksubst (fun n => (σ₀ n).lsh) (fun n => (σ₁ n).lsh) A)
  | llam l A => llam l (ksubst (fun n => (σ₀ n).lsh) (fun n => (σ₁ n).lsh) A)
  | lapp l A c => lapp l (ksubst σ₀ σ₁ A) c

/-- Substitute for level variables. -/
def lsubst (σ : Nat → Lvl α) : Ty α → Ty α
  | tvar n => tvar n
  | arr A B => arr (lsubst σ A) (lsubst σ B)
  | all k A => all (k.lsubst σ) (lsubst σ A)
  | lam k A => lam (k.lsubst σ) (lsubst σ A)
  | app k A B => app (k.lsubst σ) (lsubst σ A) (lsubst σ B)
  | kall0 A => kall0 (lsubst σ A)
  | kall1 A => kall1 (lsubst σ A)
  | pack k A => pack (k.lsubst σ) (lsubst σ A)
  | unpack k A => unpack (k.lsubst σ) (lsubst σ A)
  | apack l k A => apack (l.subst σ) (k.lsubst σ) (lsubst σ A)
  | aunpack l k A => aunpack (l.subst σ) (k.lsubst σ) (lsubst σ A)
  | lall l A => lall (l.subst σ) (lsubst (Lvl.up σ) A)
  | llam l A => llam (l.subst σ) (lsubst (Lvl.up σ) A)
  | lapp l A c => lapp (l.subst σ) (lsubst σ A) (c.subst σ)

/-- Shift the level variables, to enter a level binder. -/
abbrev lsh (A : Ty α) : Ty α := A.lsubst fun i => .var (i + 1)

def tcons (B : Ty α) (σ : Nat → Ty α) : Nat → Ty α
  | 0 => B
  | n + 1 => σ n

def tup (σ : Nat → Ty α) : Nat → Ty α := tcons (tvar 0) (fun n => tren Nat.succ (σ n))

/-- Substitute for type variables; the substituted types are shifted under level binders. -/
def tsubst (σ : Nat → Ty α) : Ty α → Ty α
  | tvar n => σ n
  | arr A B => arr (tsubst σ A) (tsubst σ B)
  | all k A => all k (tsubst (tup σ) A)
  | lam k A => lam k (tsubst (tup σ) A)
  | app k A B => app k (tsubst σ A) (tsubst σ B)
  | kall0 A => kall0 (tsubst (fun n => kren Nat.succ id (σ n)) A)
  | kall1 A => kall1 (tsubst (fun n => kren id Nat.succ (σ n)) A)
  | pack k A => pack k (tsubst σ A)
  | unpack k A => unpack k (tsubst σ A)
  | apack l k A => apack l k (tsubst σ A)
  | aunpack l k A => aunpack l k (tsubst σ A)
  | lall l A => lall l (tsubst (fun n => (σ n).lsh) A)
  | llam l A => llam l (tsubst (fun n => (σ n).lsh) A)
  | lapp l A c => lapp l (tsubst σ A) c

def inst (A B : Ty α) : Ty α := tsubst (tcons B tvar) A

def kinst0 (A : Ty α) (K : Kind α) : Ty α := ksubst (Kind.kcons K .kvar) .dvar A
def kinst1 (A : Ty α) (K : Kind α) : Ty α := ksubst .kvar (Kind.kcons K .dvar) A

/-- Instantiate the innermost level variable. -/
def linst (A : Ty α) (c : Lvl α) : Ty α := lsubst (Lvl.lcons c Lvl.var) A

def nat : Ty α := all .star (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0)))

end Ty

open Ty

/-! ## Kinding -/

abbrev KCtx (α : Type) := Nat → Kind α

def kcons (k : Kind α) (Δ : KCtx α) : KCtx α
  | 0 => k
  | n + 1 => Δ n

def KCtx.klift0 (Δ : KCtx α) : KCtx α := fun n => (Δ n).sh₀
def KCtx.klift1 (Δ : KCtx α) : KCtx α := fun n => (Δ n).sh₁
/-- Shift the level variables of a kind context, to enter a level binder. -/
def KCtx.llift (Δ : KCtx α) : KCtx α := fun n => (Δ n).lsh

/-! ## Type-level reduction -/

inductive TStep : Ty α → Ty α → Prop where
  | beta (k k' : Kind α) (A B : Ty α) : TStep (app k (lam k' A) B) (Ty.inst A B)
  | unpackPack (k : Kind α) (A : Ty α) : k.DynFree → TStep (unpack k (pack k A)) A
  | aunpackApack (l : Lvl α) (k : Kind α) (A : Ty α) : TStep (aunpack l k (apack l k A)) A
  | lbeta (l l' : Lvl α) (A : Ty α) (c : Lvl α) : TStep (lapp l (llam l' A) c) (A.linst c)
  | arrL {A A' : Ty α} (B : Ty α) : TStep A A' → TStep (arr A B) (arr A' B)
  | arrR (A : Ty α) {B B' : Ty α} : TStep B B' → TStep (arr A B) (arr A B')
  | all (k : Kind α) {A A' : Ty α} : TStep A A' → TStep (all k A) (all k A')
  | lam (k : Kind α) {A A' : Ty α} : TStep A A' → TStep (lam k A) (lam k A')
  | appL (k : Kind α) {A A' : Ty α} (B : Ty α) : TStep A A' → TStep (app k A B) (app k A' B)
  | appR (k : Kind α) (A : Ty α) {B B' : Ty α} : TStep B B' → TStep (app k A B) (app k A B')
  | kall0 {A A' : Ty α} : TStep A A' → TStep (kall0 A) (kall0 A')
  | kall1 {A A' : Ty α} : TStep A A' → TStep (kall1 A) (kall1 A')
  | pack (k : Kind α) {A A' : Ty α} : TStep A A' → TStep (pack k A) (pack k A')
  | unpack (k : Kind α) {A A' : Ty α} : TStep A A' → TStep (unpack k A) (unpack k A')
  | apack (l : Lvl α) (k : Kind α) {A A' : Ty α} :
      TStep A A' → TStep (apack l k A) (apack l k A')
  | aunpack (l : Lvl α) (k : Kind α) {A A' : Ty α} :
      TStep A A' → TStep (aunpack l k A) (aunpack l k A')
  | lall (l : Lvl α) {A A' : Ty α} : TStep A A' → TStep (lall l A) (lall l A')
  | llam (l : Lvl α) {A A' : Ty α} : TStep A A' → TStep (llam l A) (llam l A')
  | lapp (l : Lvl α) {A A' : Ty α} (c : Lvl α) : TStep A A' → TStep (lapp l A c) (lapp l A' c)

inductive TSteps : Ty α → Ty α → Prop where
  | refl (A : Ty α) : TSteps A A
  | step {A B C : Ty α} : TStep A B → TSteps B C → TSteps A C

def TJoin (A B : Ty α) : Prop := ∃ C, TSteps A C ∧ TSteps B C

theorem TSteps.join_left {A B : Ty α} (s : TSteps A B) : TJoin A B := ⟨B, s, TSteps.refl B⟩

theorem TJoin.symm {A B : Ty α} (j : TJoin A B) : TJoin B A := by
  obtain ⟨C, h₁, h₂⟩ := j
  exact ⟨C, h₂, h₁⟩

section Kinding

variable [DecidableEq α] [AtomOrder α]

inductive Kinded : List (Lvl α) → KCtx α → Ty α → Kind α → Prop where
  | tvar {Λ : List (Lvl α)} {Δ : KCtx α} (n : Nat) : Kinded Λ Δ (tvar n) (Δ n)
  | arr {Λ : List (Lvl α)} {Δ : KCtx α} {A B : Ty α} :
      Kinded Λ Δ A .star → Kinded Λ Δ B .star → Kinded Λ Δ (arr A B) .star
  | all {Λ : List (Lvl α)} {Δ : KCtx α} {k : Kind α} {A : Ty α} :
      Kinded Λ (kcons k Δ) A .star → Kinded Λ Δ (all k A) .star
  | lam {Λ : List (Lvl α)} {Δ : KCtx α} {k₁ k₂ : Kind α} {A : Ty α} :
      Kinded Λ (kcons k₁ Δ) A k₂ → Kinded Λ Δ (lam k₁ A) (.arr k₁ k₂)
  | app {Λ : List (Lvl α)} {Δ : KCtx α} {k₁ k₂ : Kind α} {A B : Ty α} :
      Kinded Λ Δ A (.arr k₁ k₂) → Kinded Λ Δ B k₁ → Kinded Λ Δ (app k₁ A B) k₂
  | kall0 {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} :
      Kinded Λ Δ.klift0 A .star → Kinded Λ Δ (kall0 A) .star
  | kall1 {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} :
      Kinded Λ Δ.klift1 A .star → Kinded Λ Δ (kall1 A) .star
  | pack {Λ : List (Lvl α)} {Δ : KCtx α} {k : Kind α} {A : Ty α} :
      Kinded Λ Δ A k → k.DynFree → Kinded Λ Δ (pack k A) .dyn
  | unpack {Λ : List (Lvl α)} {Δ : KCtx α} {k : Kind α} {A : Ty α} :
      Kinded Λ Δ A .dyn → k.DynFree → Kinded Λ Δ (unpack k A) k
  | apack {Λ : List (Lvl α)} {Δ : KCtx α} {l : Lvl α} {k : Kind α} {A : Ty α} :
      Kinded Λ Δ A k → k.Fits Λ l → Kinded Λ Δ (apack l k A) (.atom l)
  | aunpack {Λ : List (Lvl α)} {Δ : KCtx α} {l : Lvl α} {k : Kind α} {A : Ty α} :
      Kinded Λ Δ A (.atom l) → k.Fits Λ l → Kinded Λ Δ (aunpack l k A) k
  | lall {Λ : List (Lvl α)} {Δ : KCtx α} {l : Lvl α} {A : Ty α} :
      Kinded (l :: Λ) Δ.llift A .star → Kinded Λ Δ (lall l A) .star
  | llam {Λ : List (Lvl α)} {Δ : KCtx α} {l : Lvl α} {k : Kind α} {A : Ty α} :
      Kinded (l :: Λ) Δ.llift A k.lsh → Kinded Λ Δ (llam l A) (.lfam l k)
  | lapp {Λ : List (Lvl α)} {Δ : KCtx α} {l c : Lvl α} {k : Kind α} {A : Ty α} :
      Kinded Λ Δ A (.lfam l k) → lle Λ c l = true → Kinded Λ Δ (lapp l A c) k

theorem Kinded.ren {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} {k : Kind α} (h : Kinded Λ Δ A k) :
    ∀ {Δ' : KCtx α} {ξ : Nat → Nat}, (∀ n, Δ' (ξ n) = Δ n) → Kinded Λ Δ' (tren ξ A) k := by
  induction h with
  | tvar n => intro Δ' ξ hξ; rw [← hξ n]; exact Kinded.tvar _
  | arr _ _ ih₁ ih₂ => intro Δ' ξ hξ; exact Kinded.arr (ih₁ hξ) (ih₂ hξ)
  | all _ ih =>
      intro Δ' ξ hξ
      exact Kinded.all (ih fun n => by cases n <;> simp [kcons, upRen, hξ])
  | lam _ ih =>
      intro Δ' ξ hξ
      exact Kinded.lam (ih fun n => by cases n <;> simp [kcons, upRen, hξ])
  | app _ _ ih₁ ih₂ => intro Δ' ξ hξ; exact Kinded.app (ih₁ hξ) (ih₂ hξ)
  | kall0 _ ih => intro Δ' ξ hξ; exact Kinded.kall0 (ih fun n => by simp [KCtx.klift0, hξ])
  | kall1 _ ih => intro Δ' ξ hξ; exact Kinded.kall1 (ih fun n => by simp [KCtx.klift1, hξ])
  | pack _ hk ih => intro Δ' ξ hξ; exact Kinded.pack (ih hξ) hk
  | unpack _ hk ih => intro Δ' ξ hξ; exact Kinded.unpack (ih hξ) hk
  | apack _ hk ih => intro Δ' ξ hξ; exact Kinded.apack (ih hξ) hk
  | aunpack _ hk ih => intro Δ' ξ hξ; exact Kinded.aunpack (ih hξ) hk
  | lall _ ih => intro Δ' ξ hξ; exact Kinded.lall (ih fun n => by simp [KCtx.llift, hξ])
  | llam _ ih => intro Δ' ξ hξ; exact Kinded.llam (ih fun n => by simp [KCtx.llift, hξ])
  | lapp _ hc ih => intro Δ' ξ hξ; exact Kinded.lapp (ih hξ) hc

theorem Kinded.kren {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} {k : Kind α} (h : Kinded Λ Δ A k) :
    ∀ (ξ₀ ξ₁ : Nat → Nat),
      Kinded Λ (fun n => (Δ n).ren ξ₀ ξ₁) (Ty.kren ξ₀ ξ₁ A) (k.ren ξ₀ ξ₁) := by
  induction h with
  | tvar n => intro ξ₀ ξ₁; exact Kinded.tvar n
  | arr _ _ ih₁ ih₂ => intro ξ₀ ξ₁; exact Kinded.arr (ih₁ ξ₀ ξ₁) (ih₂ ξ₀ ξ₁)
  | @all Λ Δ k A _ ih =>
      intro ξ₀ ξ₁
      refine Kinded.all ?_
      have e : (fun n => (kcons k Δ n).ren ξ₀ ξ₁) =
          kcons (k.ren ξ₀ ξ₁) (fun n => (Δ n).ren ξ₀ ξ₁) := by
        funext n; cases n <;> rfl
      have := ih ξ₀ ξ₁
      rw [e] at this
      exact this
  | @lam Λ Δ k₁ k₂ A _ ih =>
      intro ξ₀ ξ₁
      refine Kinded.lam ?_
      have e : (fun n => (kcons k₁ Δ n).ren ξ₀ ξ₁) =
          kcons (k₁.ren ξ₀ ξ₁) (fun n => (Δ n).ren ξ₀ ξ₁) := by
        funext n; cases n <;> rfl
      have := ih ξ₀ ξ₁
      rw [e] at this
      exact this
  | app _ _ ih₁ ih₂ => intro ξ₀ ξ₁; exact Kinded.app (ih₁ ξ₀ ξ₁) (ih₂ ξ₀ ξ₁)
  | @kall0 Λ Δ A _ ih =>
      intro ξ₀ ξ₁
      refine Kinded.kall0 ?_
      have := ih (upRen ξ₀) ξ₁
      have e : (fun n => (Δ.klift0 n).ren (upRen ξ₀) ξ₁) =
          KCtx.klift0 (fun n => (Δ n).ren ξ₀ ξ₁) := by
        funext n
        show ((Δ n).ren Nat.succ id).ren (upRen ξ₀) ξ₁ = ((Δ n).ren ξ₀ ξ₁).ren Nat.succ id
        rw [Kind.ren_ren, Kind.ren_ren]; rfl
      rw [e] at this
      exact this
  | @kall1 Λ Δ A _ ih =>
      intro ξ₀ ξ₁
      refine Kinded.kall1 ?_
      have := ih ξ₀ (upRen ξ₁)
      have e : (fun n => (Δ.klift1 n).ren ξ₀ (upRen ξ₁)) =
          KCtx.klift1 (fun n => (Δ n).ren ξ₀ ξ₁) := by
        funext n
        show ((Δ n).ren id Nat.succ).ren ξ₀ (upRen ξ₁) = ((Δ n).ren ξ₀ ξ₁).ren id Nat.succ
        rw [Kind.ren_ren, Kind.ren_ren]; rfl
      rw [e] at this
      exact this
  | pack _ hk ih => intro ξ₀ ξ₁; exact Kinded.pack (ih ξ₀ ξ₁) (hk.ren ξ₀ ξ₁)
  | unpack _ hk ih => intro ξ₀ ξ₁; exact Kinded.unpack (ih ξ₀ ξ₁) (hk.ren ξ₀ ξ₁)
  | @apack Λ Δ l k A _ hk ih =>
      intro ξ₀ ξ₁
      have e := hk.ren_eq ξ₀ ξ₁
      have h := ih ξ₀ ξ₁
      rw [e] at h
      show Kinded _ _ (Ty.apack l (k.ren ξ₀ ξ₁) _) _
      rw [e]
      exact Kinded.apack h hk
  | @aunpack Λ Δ l k A _ hk ih =>
      intro ξ₀ ξ₁
      have e := hk.ren_eq ξ₀ ξ₁
      show Kinded _ _ (Ty.aunpack l (k.ren ξ₀ ξ₁) _) (k.ren ξ₀ ξ₁)
      rw [e]
      exact Kinded.aunpack (ih ξ₀ ξ₁) hk
  | @lall Λ Δ l A _ ih =>
      intro ξ₀ ξ₁
      refine Kinded.lall ?_
      have := ih ξ₀ ξ₁
      have e : (fun n => (Δ.llift n).ren ξ₀ ξ₁) = KCtx.llift (fun n => (Δ n).ren ξ₀ ξ₁) := by
        funext n
        exact Kind.ren_lsubst _ ξ₀ ξ₁ (Δ n)
      rw [e] at this
      exact this
  | @llam Λ Δ l k A _ ih =>
      intro ξ₀ ξ₁
      refine Kinded.llam ?_
      have := ih ξ₀ ξ₁
      have e : (fun n => (Δ.llift n).ren ξ₀ ξ₁) = KCtx.llift (fun n => (Δ n).ren ξ₀ ξ₁) := by
        funext n
        exact Kind.ren_lsubst _ ξ₀ ξ₁ (Δ n)
      have ek : k.lsh.ren ξ₀ ξ₁ = (k.ren ξ₀ ξ₁).lsh := Kind.ren_lsubst _ ξ₀ ξ₁ k
      rw [e, ek] at this
      exact this
  | lapp _ hc ih => intro ξ₀ ξ₁; exact Kinded.lapp (ih ξ₀ ξ₁) hc

theorem Kinded.ksubst {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} {k : Kind α} (h : Kinded Λ Δ A k) :
    ∀ (σ₀ σ₁ : Nat → Kind α), (∀ n, (σ₀ n).DynFree) →
      Kinded Λ (fun n => (Δ n).subst σ₀ σ₁) (Ty.ksubst σ₀ σ₁ A) (k.subst σ₀ σ₁) := by
  induction h with
  | tvar n => intro σ₀ σ₁ _; exact Kinded.tvar n
  | arr _ _ ih₁ ih₂ => intro σ₀ σ₁ hσ; exact Kinded.arr (ih₁ σ₀ σ₁ hσ) (ih₂ σ₀ σ₁ hσ)
  | @all Λ Δ k A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.all ?_
      have e : (fun n => (kcons k Δ n).subst σ₀ σ₁) =
          kcons (k.subst σ₀ σ₁) (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n; cases n <;> rfl
      have := ih σ₀ σ₁ hσ
      rw [e] at this
      exact this
  | @lam Λ Δ k₁ k₂ A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.lam ?_
      have e : (fun n => (kcons k₁ Δ n).subst σ₀ σ₁) =
          kcons (k₁.subst σ₀ σ₁) (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n; cases n <;> rfl
      have := ih σ₀ σ₁ hσ
      rw [e] at this
      exact this
  | app _ _ ih₁ ih₂ => intro σ₀ σ₁ hσ; exact Kinded.app (ih₁ σ₀ σ₁ hσ) (ih₂ σ₀ σ₁ hσ)
  | @kall0 Λ Δ A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.kall0 ?_
      have hσ' : ∀ n, ((Ty.kup₀ σ₀ σ₁).1 n).DynFree := fun n => by
        cases n with
        | zero => trivial
        | succ n => exact (hσ n).ren _ _
      have := ih (Ty.kup₀ σ₀ σ₁).1 (Ty.kup₀ σ₀ σ₁).2 hσ'
      have e : (fun n => (Δ.klift0 n).subst (Ty.kup₀ σ₀ σ₁).1 (Ty.kup₀ σ₀ σ₁).2) =
          KCtx.klift0 (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n
        show ((Δ n).ren Nat.succ id).subst _ _ = ((Δ n).subst σ₀ σ₁).ren Nat.succ id
        rw [Kind.subst_ren, Kind.ren_subst]; rfl
      rw [e] at this
      exact this
  | @kall1 Λ Δ A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.kall1 ?_
      have hσ' : ∀ n, ((Ty.kup₁ σ₀ σ₁).1 n).DynFree := fun n => (hσ n).ren _ _
      have := ih (Ty.kup₁ σ₀ σ₁).1 (Ty.kup₁ σ₀ σ₁).2 hσ'
      have e : (fun n => (Δ.klift1 n).subst (Ty.kup₁ σ₀ σ₁).1 (Ty.kup₁ σ₀ σ₁).2) =
          KCtx.klift1 (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n
        show ((Δ n).ren id Nat.succ).subst _ _ = ((Δ n).subst σ₀ σ₁).ren id Nat.succ
        rw [Kind.subst_ren, Kind.ren_subst]; rfl
      rw [e] at this
      exact this
  | pack _ hk ih => intro σ₀ σ₁ hσ; exact Kinded.pack (ih σ₀ σ₁ hσ) (hk.subst hσ)
  | unpack _ hk ih => intro σ₀ σ₁ hσ; exact Kinded.unpack (ih σ₀ σ₁ hσ) (hk.subst hσ)
  | @apack Λ Δ l k A _ hk ih =>
      intro σ₀ σ₁ hσ
      have e := hk.subst_eq σ₀ σ₁
      have h := ih σ₀ σ₁ hσ
      rw [e] at h
      show Kinded _ _ (Ty.apack l (k.subst σ₀ σ₁) _) _
      rw [e]
      exact Kinded.apack h hk
  | @aunpack Λ Δ l k A _ hk ih =>
      intro σ₀ σ₁ hσ
      have e := hk.subst_eq σ₀ σ₁
      show Kinded _ _ (Ty.aunpack l (k.subst σ₀ σ₁) _) (k.subst σ₀ σ₁)
      rw [e]
      exact Kinded.aunpack (ih σ₀ σ₁ hσ) hk
  | @lall Λ Δ l A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.lall ?_
      have := ih (fun n => (σ₀ n).lsh) (fun n => (σ₁ n).lsh) fun n => (hσ n).lsubst _
      have e : (fun n => (Δ.llift n).subst (fun n => (σ₀ n).lsh) (fun n => (σ₁ n).lsh)) =
          KCtx.llift (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n
        exact (Kind.subst_lsubst _ σ₀ σ₁ (Δ n)).symm
      rw [e] at this
      exact this
  | @llam Λ Δ l k A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.llam ?_
      have := ih (fun n => (σ₀ n).lsh) (fun n => (σ₁ n).lsh) fun n => (hσ n).lsubst _
      have e : (fun n => (Δ.llift n).subst (fun n => (σ₀ n).lsh) (fun n => (σ₁ n).lsh)) =
          KCtx.llift (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n
        exact (Kind.subst_lsubst _ σ₀ σ₁ (Δ n)).symm
      have ek : k.lsh.subst (fun n => (σ₀ n).lsh) (fun n => (σ₁ n).lsh) = (k.subst σ₀ σ₁).lsh :=
        (Kind.subst_lsubst _ σ₀ σ₁ k).symm
      rw [e, ek] at this
      exact this
  | lapp _ hc ih => intro σ₀ σ₁ hσ; exact Kinded.lapp (ih σ₀ σ₁ hσ) hc

/-- **Level substitution** along a map that respects the forced order. -/
theorem Kinded.lsubst {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} {k : Kind α} (h : Kinded Λ Δ A k) :
    ∀ {Λ' : List (Lvl α)} {σ : Nat → Lvl α}, LMap Λ Λ' σ →
      Kinded Λ' (fun n => (Δ n).lsubst σ) (A.lsubst σ) (k.lsubst σ) := by
  induction h with
  | tvar n => intro Λ' σ _; exact Kinded.tvar n
  | arr _ _ ih₁ ih₂ => intro Λ' σ hσ; exact Kinded.arr (ih₁ hσ) (ih₂ hσ)
  | @all Λ Δ k A _ ih =>
      intro Λ' σ hσ
      refine Kinded.all ?_
      have e : (fun n => (kcons k Δ n).lsubst σ) =
          kcons (k.lsubst σ) (fun n => (Δ n).lsubst σ) := by
        funext n; cases n <;> rfl
      have := ih hσ
      rw [e] at this
      exact this
  | @lam Λ Δ k₁ k₂ A _ ih =>
      intro Λ' σ hσ
      refine Kinded.lam ?_
      have e : (fun n => (kcons k₁ Δ n).lsubst σ) =
          kcons (k₁.lsubst σ) (fun n => (Δ n).lsubst σ) := by
        funext n; cases n <;> rfl
      have := ih hσ
      rw [e] at this
      exact this
  | app _ _ ih₁ ih₂ => intro Λ' σ hσ; exact Kinded.app (ih₁ hσ) (ih₂ hσ)
  | @kall0 Λ Δ A _ ih =>
      intro Λ' σ hσ
      refine Kinded.kall0 ?_
      have := ih hσ
      have e : (fun n => (Δ.klift0 n).lsubst σ) = KCtx.klift0 (fun n => (Δ n).lsubst σ) := by
        funext n
        exact (Kind.ren_lsubst σ Nat.succ id (Δ n)).symm
      rw [e] at this
      exact this
  | @kall1 Λ Δ A _ ih =>
      intro Λ' σ hσ
      refine Kinded.kall1 ?_
      have := ih hσ
      have e : (fun n => (Δ.klift1 n).lsubst σ) = KCtx.klift1 (fun n => (Δ n).lsubst σ) := by
        funext n
        exact (Kind.ren_lsubst σ id Nat.succ (Δ n)).symm
      rw [e] at this
      exact this
  | pack _ hk ih => intro Λ' σ hσ; exact Kinded.pack (ih hσ) (hk.lsubst σ)
  | unpack _ hk ih => intro Λ' σ hσ; exact Kinded.unpack (ih hσ) (hk.lsubst σ)
  | apack _ hk ih => intro Λ' σ hσ; exact Kinded.apack (ih hσ) (hk.lsubst hσ)
  | aunpack _ hk ih => intro Λ' σ hσ; exact Kinded.aunpack (ih hσ) (hk.lsubst hσ)
  | @lall Λ Δ l A _ ih =>
      intro Λ' σ hσ
      refine Kinded.lall ?_
      have := ih (hσ.up l)
      have e : (fun n => (Δ.llift n).lsubst (Lvl.up σ)) = KCtx.llift (fun n => (Δ n).lsubst σ) := by
        funext n
        exact Kind.lsh_lsubst_up σ (Δ n)
      rw [e] at this
      exact this
  | @llam Λ Δ l k A _ ih =>
      intro Λ' σ hσ
      refine Kinded.llam ?_
      have := ih (hσ.up l)
      have e : (fun n => (Δ.llift n).lsubst (Lvl.up σ)) = KCtx.llift (fun n => (Δ n).lsubst σ) := by
        funext n
        exact Kind.lsh_lsubst_up σ (Δ n)
      rw [e, Kind.lsh_lsubst_up] at this
      exact this
  | lapp _ hc ih => intro Λ' σ hσ; exact Kinded.lapp (ih hσ) (hσ.lle_pres hc)

theorem Kinded.subst {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} {k : Kind α} (h : Kinded Λ Δ A k) :
    ∀ {Δ' : KCtx α} {σ : Nat → Ty α}, (∀ n, Kinded Λ Δ' (σ n) (Δ n)) →
      Kinded Λ Δ' (tsubst σ A) k := by
  induction h with
  | tvar n => intro Δ' σ hσ; exact hσ n
  | arr _ _ ih₁ ih₂ => intro Δ' σ hσ; exact Kinded.arr (ih₁ hσ) (ih₂ hσ)
  | @all Λ Δ k A _ ih =>
      intro Δ' σ hσ
      refine Kinded.all (ih fun n => ?_)
      cases n with
      | zero => exact Kinded.tvar 0
      | succ n => exact (hσ n).ren fun _ => rfl
  | @lam Λ Δ k₁ k₂ A _ ih =>
      intro Δ' σ hσ
      refine Kinded.lam (ih fun n => ?_)
      cases n with
      | zero => exact Kinded.tvar 0
      | succ n => exact (hσ n).ren fun _ => rfl
  | app _ _ ih₁ ih₂ => intro Δ' σ hσ; exact Kinded.app (ih₁ hσ) (ih₂ hσ)
  | kall0 _ ih => intro Δ' σ hσ; exact Kinded.kall0 (ih fun n => (hσ n).kren Nat.succ id)
  | kall1 _ ih => intro Δ' σ hσ; exact Kinded.kall1 (ih fun n => (hσ n).kren id Nat.succ)
  | pack _ hk ih => intro Δ' σ hσ; exact Kinded.pack (ih hσ) hk
  | unpack _ hk ih => intro Δ' σ hσ; exact Kinded.unpack (ih hσ) hk
  | apack _ hk ih => intro Δ' σ hσ; exact Kinded.apack (ih hσ) hk
  | aunpack _ hk ih => intro Δ' σ hσ; exact Kinded.aunpack (ih hσ) hk
  | @lall Λ Δ l A _ ih =>
      intro Δ' σ hσ
      exact Kinded.lall (ih fun n => (hσ n).lsubst (LMap.weaken l Λ))
  | @llam Λ Δ l k A _ ih =>
      intro Δ' σ hσ
      exact Kinded.llam (ih fun n => (hσ n).lsubst (LMap.weaken l Λ))
  | lapp _ hc ih => intro Δ' σ hσ; exact Kinded.lapp (ih hσ) hc

theorem Kinded.inst {Λ : List (Lvl α)} {Δ : KCtx α} {k k' : Kind α} {A B : Ty α}
    (hA : Kinded Λ (kcons k Δ) A k') (hB : Kinded Λ Δ B k) : Kinded Λ Δ (Ty.inst A B) k' :=
  hA.subst fun n => by
    cases n with
    | zero => exact hB
    | succ n => exact Kinded.tvar n

theorem Kinded.kinst0 {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} (hA : Kinded Λ Δ.klift0 A .star)
    {K : Kind α} (hK : K.DynFree) : Kinded Λ Δ (Ty.kinst0 A K) .star := by
  have h := hA.ksubst (Kind.kcons K .kvar) .dvar fun n => by
    cases n with
    | zero => exact hK
    | succ n => trivial
  have e : (fun n => (Δ.klift0 n).subst (Kind.kcons K .kvar) .dvar) = Δ := by
    funext n
    show ((Δ n).ren Nat.succ id).subst _ _ = Δ n
    rw [Kind.subst_ren]
    exact Kind.subst_var (Δ n)
  rw [e] at h
  exact h

theorem Kinded.kinst1 {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} (hA : Kinded Λ Δ.klift1 A .star)
    (K : Kind α) : Kinded Λ Δ (Ty.kinst1 A K) .star := by
  have h := hA.ksubst .kvar (Kind.kcons K .dvar) fun _ => trivial
  have e : (fun n => (Δ.klift1 n).subst .kvar (Kind.kcons K .dvar)) = Δ := by
    funext n
    show ((Δ n).ren id Nat.succ).subst _ _ = Δ n
    rw [Kind.subst_ren]
    exact Kind.subst_var (Δ n)
  rw [e] at h
  exact h

/-- Instantiating a level variable at a level `c ≤ l`. -/
theorem Kinded.linst (htr : LtTrans α) {Λ : List (Lvl α)} {Δ : KCtx α} {l c : Lvl α} {A : Ty α}
    {k : Kind α} (hA : Kinded (l :: Λ) Δ.llift A k) (hc : lle Λ c l = true) :
    Kinded Λ Δ (A.linst c) (k.lsubst (Lvl.lcons c Lvl.var)) := by
  have h := hA.lsubst (LMap.inst htr hc)
  have e : (fun n => (Δ.llift n).lsubst (Lvl.lcons c Lvl.var)) = Δ := by
    funext n
    exact Kind.lsh_lsubst_lcons c (Δ n)
  rw [e] at h
  exact h

theorem Kinded.nat (Λ : List (Lvl α)) (Δ : KCtx α) : Kinded Λ Δ Ty.nat .star :=
  Kinded.all (Kinded.arr (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0))
    (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0)))

theorem Kinded.step (htr : LtTrans α) {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} {k : Kind α}
    (h : Kinded Λ Δ A k) {B : Ty α} (s : TStep A B) : Kinded Λ Δ B k := by
  induction s generalizing Λ Δ k with
  | beta k₁ k' A B =>
      cases h with
      | app hA hB =>
          cases hA with
          | lam hA' => exact hA'.inst hB
  | unpackPack k A _ =>
      cases h with
      | unpack hX _ =>
          cases hX with
          | pack hA _ => exact hA
  | aunpackApack l k A =>
      cases h with
      | aunpack hX _ =>
          cases hX with
          | apack hA _ => exact hA
  | lbeta l l' A c =>
      cases h with
      | lapp hF hc =>
          cases hF with
          | llam hA =>
              have h' := Kinded.linst htr hA hc
              rw [Kind.lsh_lsubst_lcons] at h'
              exact h'
  | arrL _ _ ih => cases h with | arr h₁ h₂ => exact Kinded.arr (ih h₁) h₂
  | arrR _ _ ih => cases h with | arr h₁ h₂ => exact Kinded.arr h₁ (ih h₂)
  | all _ _ ih => cases h with | all h₁ => exact Kinded.all (ih h₁)
  | lam _ _ ih => cases h with | lam h₁ => exact Kinded.lam (ih h₁)
  | appL _ _ _ ih => cases h with | app h₁ h₂ => exact Kinded.app (ih h₁) h₂
  | appR _ _ _ ih => cases h with | app h₁ h₂ => exact Kinded.app h₁ (ih h₂)
  | kall0 _ ih => cases h with | kall0 h₁ => exact Kinded.kall0 (ih h₁)
  | kall1 _ ih => cases h with | kall1 h₁ => exact Kinded.kall1 (ih h₁)
  | pack _ _ ih => cases h with | pack h₁ hk => exact Kinded.pack (ih h₁) hk
  | unpack _ _ ih => cases h with | unpack h₁ hk => exact Kinded.unpack (ih h₁) hk
  | apack _ _ _ ih => cases h with | apack h₁ hk => exact Kinded.apack (ih h₁) hk
  | aunpack _ _ _ ih => cases h with | aunpack h₁ hk => exact Kinded.aunpack (ih h₁) hk
  | lall _ _ ih => cases h with | lall h₁ => exact Kinded.lall (ih h₁)
  | llam _ _ ih => cases h with | llam h₁ => exact Kinded.llam (ih h₁)
  | lapp _ _ _ ih => cases h with | lapp h₁ hc => exact Kinded.lapp (ih h₁) hc

theorem Kinded.steps (htr : LtTrans α) {Λ : List (Lvl α)} {Δ : KCtx α} {A B : Ty α} {k : Kind α}
    (h : Kinded Λ Δ A k) (s : TSteps A B) : Kinded Λ Δ B k := by
  induction s with
  | refl => exact h
  | step s _ ih => exact ih (h.step htr s)

end Kinding

/-! ## A sound, fuel-bounded type normalizer -/

section Normalizer

variable [DecidableEq α]

def tappCong (k : Kind α) (A B : Ty α) (sA sB : Option (Ty α)) : Option (Ty α) :=
  match sA with
  | some A' => some (app k A' B)
  | none => sB.map (app k A)

def tappStep (k : Kind α) (A B : Ty α) (sA sB : Option (Ty α)) : Option (Ty α) :=
  match A with
  | lam _ A₀ => some (Ty.inst A₀ B)
  | _ => tappCong k A B sA sB

def tlappStep (l : Lvl α) (A : Ty α) (c : Lvl α) (sA : Option (Ty α)) : Option (Ty α) :=
  match A with
  | llam _ A₀ => some (A₀.linst c)
  | _ => sA.map fun A' => lapp l A' c

/-- The atom-level unpack-of-pack redex, when levels and kinds agree. -/
def aunpackRedex (l : Lvl α) (k : Kind α) (A : Ty α) : Option (Ty α) :=
  match A with
  | apack l' k' A₀ => if l' = l ∧ k' = k then some A₀ else none
  | _ => none

/-- The unpack-of-pack redex, when the kinds agree and are dyn-free. -/
def unpackRedex (k : Kind α) (A : Ty α) : Option (Ty α) :=
  match A with
  | pack k' A₀ => if k' = k ∧ k.dynFree = true then some A₀ else none
  | _ => none

def tstep : Ty α → Option (Ty α)
  | tvar _ => none
  | arr A B =>
      match tstep A with
      | some A' => some (arr A' B)
      | none => (tstep B).map (arr A)
  | all k A => (tstep A).map (all k)
  | lam k A => (tstep A).map (lam k)
  | app k A B => tappStep k A B (tstep A) (tstep B)
  | kall0 A => (tstep A).map kall0
  | kall1 A => (tstep A).map kall1
  | pack k A => (tstep A).map (pack k)
  | unpack k A =>
      match unpackRedex k A with
      | some B => some B
      | none => (tstep A).map (unpack k)
  | apack l k A => (tstep A).map (apack l k)
  | aunpack l k A =>
      match aunpackRedex l k A with
      | some B => some B
      | none => (tstep A).map (aunpack l k)
  | lall l A => (tstep A).map (lall l)
  | llam l A => (tstep A).map (llam l)
  | lapp l A c => tlappStep l A c (tstep A)

omit [DecidableEq α] in
theorem tappCong_sound {k : Kind α} {A B C : Ty α} {sA sB : Option (Ty α)}
    (hA : ∀ A', sA = some A' → TStep A A') (hB : ∀ B', sB = some B' → TStep B B')
    (h : tappCong k A B sA sB = some C) : TStep (app k A B) C := by
  unfold tappCong at h
  cases sA with
  | some A' => cases h; exact TStep.appL _ _ (hA A' rfl)
  | none =>
      cases sB with
      | none => cases h
      | some B' => cases h; exact TStep.appR _ _ (hB B' rfl)

omit [DecidableEq α] in
theorem tappStep_sound {k : Kind α} {A B C : Ty α} {sA sB : Option (Ty α)}
    (hA : ∀ A', sA = some A' → TStep A A') (hB : ∀ B', sB = some B' → TStep B B')
    (h : tappStep k A B sA sB = some C) : TStep (app k A B) C := by
  unfold tappStep at h
  split at h
  · cases h; exact TStep.beta _ _ _ _
  · exact tappCong_sound hA hB h

omit [DecidableEq α] in
theorem tlappStep_sound {l c : Lvl α} {A C : Ty α} {sA : Option (Ty α)}
    (hA : ∀ A', sA = some A' → TStep A A') (h : tlappStep l A c sA = some C) :
    TStep (lapp l A c) C := by
  unfold tlappStep at h
  split at h
  · cases h; exact TStep.lbeta _ _ _ _
  · cases sA with
    | none => cases h
    | some A' => cases h; exact TStep.lapp _ _ (hA A' rfl)

theorem unpackRedex_sound {k : Kind α} {A B : Ty α} (h : unpackRedex k A = some B) :
    TStep (unpack k A) B := by
  unfold unpackRedex at h
  split at h
  · split at h
    · next e =>
        cases h
        obtain ⟨rfl, hk⟩ := e
        exact TStep.unpackPack _ _ ((Kind.dynFree_iff _).1 hk)
    · cases h
  · cases h

theorem aunpackRedex_sound {l : Lvl α} {k : Kind α} {A B : Ty α}
    (h : aunpackRedex l k A = some B) : TStep (aunpack l k A) B := by
  unfold aunpackRedex at h
  split at h
  · split at h
    · next e =>
        cases h
        obtain ⟨rfl, rfl⟩ := e
        exact TStep.aunpackApack _ _ _
    · cases h
  · cases h

theorem tstep_sound : ∀ {A B : Ty α}, tstep A = some B → TStep A B
  | tvar _, _, h => nomatch h
  | arr A B, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | some A' => rw [hA] at h; cases h; exact TStep.arrL _ (tstep_sound hA)
      | none =>
          rw [hA] at h
          cases hB : tstep B with
          | none => rw [hB] at h; cases h
          | some B' => rw [hB] at h; cases h; exact TStep.arrR _ (tstep_sound hB)
  | all k A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.all _ (tstep_sound hA)
  | lam k A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.lam _ (tstep_sound hA)
  | app k A B, C, h =>
      tappStep_sound (fun _ e => tstep_sound e) (fun _ e => tstep_sound e) h
  | kall0 A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.kall0 (tstep_sound hA)
  | kall1 A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.kall1 (tstep_sound hA)
  | pack k A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.pack _ (tstep_sound hA)
  | unpack k A, C, h => by
      simp only [tstep] at h
      cases hr : unpackRedex k A with
      | some B => rw [hr] at h; cases h; exact unpackRedex_sound hr
      | none =>
          rw [hr] at h
          cases hA : tstep A with
          | none => rw [hA] at h; cases h
          | some A' => rw [hA] at h; cases h; exact TStep.unpack _ (tstep_sound hA)
  | apack l k A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.apack _ _ (tstep_sound hA)
  | aunpack l k A, C, h => by
      simp only [tstep] at h
      cases hr : aunpackRedex l k A with
      | some B => rw [hr] at h; cases h; exact aunpackRedex_sound hr
      | none =>
          rw [hr] at h
          cases hA : tstep A with
          | none => rw [hA] at h; cases h
          | some A' => rw [hA] at h; cases h; exact TStep.aunpack _ _ (tstep_sound hA)
  | lall l A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.lall _ (tstep_sound hA)
  | llam l A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.llam _ (tstep_sound hA)
  | lapp l A c, C, h => tlappStep_sound (fun _ e => tstep_sound e) h

def tnf : Nat → Ty α → Ty α
  | 0, A => A
  | fuel + 1, A =>
      match tstep A with
      | some B => tnf fuel B
      | none => A

theorem tnf_steps : ∀ (fuel : Nat) (A : Ty α), TSteps A (tnf fuel A)
  | 0, A => TSteps.refl A
  | fuel + 1, A => by
      simp only [tnf]
      cases h : tstep A with
      | none => exact TSteps.refl A
      | some B => exact TSteps.step (tstep_sound h) (tnf_steps fuel B)

theorem tjoin_of_tnf {fuel : Nat} {A B : Ty α} (h : tnf fuel A = tnf fuel B) : TJoin A B :=
  ⟨tnf fuel A, tnf_steps fuel A, h ▸ tnf_steps fuel B⟩

end Normalizer

/-! ## Kind inference -/

def kctxOf (Δ : List (Kind α)) : KCtx α := fun n => (nth? Δ n).getD .star

theorem kctxOf_cons (k : Kind α) (Δ : List (Kind α)) : kctxOf (k :: Δ) = kcons k (kctxOf Δ) := by
  funext n; cases n <;> rfl

theorem kctxOf_klift0 (Δ : List (Kind α)) : kctxOf (Δ.map Kind.sh₀) = (kctxOf Δ).klift0 := by
  funext n
  show (nth? (Δ.map Kind.sh₀) n).getD .star = ((nth? Δ n).getD .star).sh₀
  rw [FL.nth?_map]
  cases nth? Δ n <;> rfl

theorem kctxOf_klift1 (Δ : List (Kind α)) : kctxOf (Δ.map Kind.sh₁) = (kctxOf Δ).klift1 := by
  funext n
  show (nth? (Δ.map Kind.sh₁) n).getD .star = ((nth? Δ n).getD .star).sh₁
  rw [FL.nth?_map]
  cases nth? Δ n <;> rfl

theorem kctxOf_llift (Δ : List (Kind α)) : kctxOf (Δ.map Kind.lsh) = (kctxOf Δ).llift := by
  funext n
  show (nth? (Δ.map Kind.lsh) n).getD .star = ((nth? Δ n).getD .star).lsh
  rw [FL.nth?_map]
  cases nth? Δ n <;> rfl

section Inference

variable [DecidableEq α] [AtomOrder α]

/-- `some ★` exactly when the argument is `some ★`. -/
def starK : Option (Kind α) → Option (Kind α)
  | some .star => some .star
  | _ => none

def arrK (x y : Option (Kind α)) : Option (Kind α) := (starK x).bind fun _ => starK y

def appK (k : Kind α) : Option (Kind α) → Option (Kind α) → Option (Kind α)
  | some (.arr k₁ k₂), some k' => if k₁ = k ∧ k' = k then some k₂ else none
  | _, _ => none

def packK (k : Kind α) : Option (Kind α) → Option (Kind α)
  | some k' => if k' = k ∧ k.dynFree = true then some .dyn else none
  | none => none

def unpackK (k : Kind α) : Option (Kind α) → Option (Kind α)
  | some .dyn => if k.dynFree = true then some k else none
  | _ => none

def apackK (Λ : List (Lvl α)) (l : Lvl α) (k : Kind α) : Option (Kind α) → Option (Kind α)
  | some k' => if k' = k ∧ k.fits Λ l = true then some (.atom l) else none
  | none => none

def aunpackK (Λ : List (Lvl α)) (l : Lvl α) (k : Kind α) : Option (Kind α) → Option (Kind α)
  | some (.atom l') => if l' = l ∧ k.fits Λ l = true then some k else none
  | _ => none

def llamK (l : Lvl α) : Option (Kind α) → Option (Kind α)
  | some k =>
      match k.unshift? with
      | some k' => some (.lfam l k')
      | none => none
  | none => none

def lappK (Λ : List (Lvl α)) (l c : Lvl α) : Option (Kind α) → Option (Kind α)
  | some (.lfam l' k) => if l' = l ∧ lle Λ c l = true then some k else none
  | _ => none

def inferKind : List (Lvl α) → List (Kind α) → Ty α → Option (Kind α)
  | _, Δ, tvar n => nth? Δ n
  | Λ, Δ, arr A B => arrK (inferKind Λ Δ A) (inferKind Λ Δ B)
  | Λ, Δ, all k A => starK (inferKind Λ (k :: Δ) A)
  | Λ, Δ, lam k A => (inferKind Λ (k :: Δ) A).map (Kind.arr k)
  | Λ, Δ, app k A B => appK k (inferKind Λ Δ A) (inferKind Λ Δ B)
  | Λ, Δ, kall0 A => starK (inferKind Λ (Δ.map Kind.sh₀) A)
  | Λ, Δ, kall1 A => starK (inferKind Λ (Δ.map Kind.sh₁) A)
  | Λ, Δ, pack k A => packK k (inferKind Λ Δ A)
  | Λ, Δ, unpack k A => unpackK k (inferKind Λ Δ A)
  | Λ, Δ, apack l k A => apackK Λ l k (inferKind Λ Δ A)
  | Λ, Δ, aunpack l k A => aunpackK Λ l k (inferKind Λ Δ A)
  | Λ, Δ, lall l A => starK (inferKind (l :: Λ) (Δ.map Kind.lsh) A)
  | Λ, Δ, llam l A => llamK l (inferKind (l :: Λ) (Δ.map Kind.lsh) A)
  | Λ, Δ, lapp l A c => lappK Λ l c (inferKind Λ Δ A)

omit [DecidableEq α] [AtomOrder α] in
theorem starK_inv {o : Option (Kind α)} {k : Kind α} (h : starK o = some k) :
    o = some .star ∧ k = .star := by
  match o, h with
  | some .star, h => cases h; exact ⟨rfl, rfl⟩

omit [DecidableEq α] [AtomOrder α] in
theorem arrK_inv {x y : Option (Kind α)} {k : Kind α} (h : arrK x y = some k) :
    x = some .star ∧ y = some .star ∧ k = .star := by
  cases hx : starK x with
  | none => rw [arrK, hx] at h; cases h
  | some s =>
      rw [arrK, hx] at h
      obtain ⟨hy, rfl⟩ := starK_inv (o := y) h
      exact ⟨(starK_inv hx).1, hy, rfl⟩

omit [AtomOrder α] in
theorem appK_inv {k r : Kind α} {x y : Option (Kind α)} (h : appK k x y = some r) :
    x = some (.arr k r) ∧ y = some k := by
  match x, y, h with
  | some (.arr k₁ k₂), some k', h =>
      change (if k₁ = k ∧ k' = k then some k₂ else none) = some r at h
      by_cases e : k₁ = k ∧ k' = k
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right e] at h; cases h

omit [AtomOrder α] in
theorem packK_inv {k r : Kind α} {x : Option (Kind α)} (h : packK k x = some r) :
    x = some k ∧ k.DynFree ∧ r = .dyn := by
  match x, h with
  | some k', h =>
      change (if k' = k ∧ k.dynFree = true then some Kind.dyn else none) = some r at h
      by_cases e : k' = k ∧ k.dynFree = true
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, hk⟩ := e
        exact ⟨rfl, (Kind.dynFree_iff _).1 hk, rfl⟩
      · rw [ite_eq_right e] at h; cases h

omit [AtomOrder α] [DecidableEq α] in
theorem unpackK_inv {k r : Kind α} {x : Option (Kind α)} (h : unpackK k x = some r) :
    x = some .dyn ∧ k.DynFree ∧ r = k := by
  match x, h with
  | some .dyn, h =>
      change (if k.dynFree = true then some k else none) = some r at h
      by_cases e : k.dynFree = true
      · rw [ite_eq_left e] at h
        cases h
        exact ⟨rfl, (Kind.dynFree_iff _).1 e, rfl⟩
      · rw [ite_eq_right e] at h; cases h

theorem apackK_inv {Λ : List (Lvl α)} {l : Lvl α} {k r : Kind α} {x : Option (Kind α)}
    (h : apackK Λ l k x = some r) : x = some k ∧ k.Fits Λ l ∧ r = .atom l := by
  match x, h with
  | some k', h =>
      change (if k' = k ∧ k.fits Λ l = true then some (Kind.atom l) else none) = some r at h
      by_cases e : k' = k ∧ k.fits Λ l = true
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, hk⟩ := e
        exact ⟨rfl, (Kind.fits_iff _ _ _).1 hk, rfl⟩
      · rw [ite_eq_right e] at h; cases h

theorem aunpackK_inv {Λ : List (Lvl α)} {l : Lvl α} {k r : Kind α} {x : Option (Kind α)}
    (h : aunpackK Λ l k x = some r) : x = some (.atom l) ∧ k.Fits Λ l ∧ r = k := by
  match x, h with
  | some (.atom l'), h =>
      change (if l' = l ∧ k.fits Λ l = true then some k else none) = some r at h
      by_cases e : l' = l ∧ k.fits Λ l = true
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, hk⟩ := e
        exact ⟨rfl, (Kind.fits_iff _ _ _).1 hk, rfl⟩
      · rw [ite_eq_right e] at h; cases h

omit [DecidableEq α] [AtomOrder α] in
theorem llamK_inv {l : Lvl α} {x : Option (Kind α)} {r : Kind α} (h : llamK l x = some r) :
    ∃ kA k, x = some kA ∧ kA.unshift? = some k ∧ r = .lfam l k := by
  cases x with
  | none => cases h
  | some kA =>
      cases hk : kA.unshift? with
      | none => simp [llamK, hk] at h
      | some k =>
          simp only [llamK, hk] at h
          cases h
          exact ⟨kA, k, rfl, hk, rfl⟩

theorem lappK_inv {Λ : List (Lvl α)} {l c : Lvl α} {x : Option (Kind α)} {r : Kind α}
    (h : lappK Λ l c x = some r) : x = some (.lfam l r) ∧ lle Λ c l = true := by
  match x, h with
  | some (.lfam l' k), h =>
      change (if l' = l ∧ lle Λ c l = true then some k else none) = some r at h
      by_cases e : l' = l ∧ lle Λ c l = true
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, hc⟩ := e
        exact ⟨rfl, hc⟩
      · rw [ite_eq_right e] at h; cases h

theorem inferKind_sound : ∀ (A : Ty α) {Λ : List (Lvl α)} {Δ : List (Kind α)} {k : Kind α},
    inferKind Λ Δ A = some k → Kinded Λ (kctxOf Δ) A k
  | tvar n, Λ, Δ, k, h => by
      have e : kctxOf Δ n = k := by
        show (nth? Δ n).getD .star = k
        rw [show nth? Δ n = some k from h]; rfl
      rw [← e]; exact Kinded.tvar n
  | arr A B, Λ, Δ, k, h => by
      obtain ⟨hA, hB, rfl⟩ := arrK_inv (x := inferKind Λ Δ A) (y := inferKind Λ Δ B) h
      exact Kinded.arr (inferKind_sound A hA) (inferKind_sound B hB)
  | all k' A, Λ, Δ, k, h => by
      obtain ⟨hA, rfl⟩ := starK_inv (o := inferKind Λ (k' :: Δ) A) h
      have ih := inferKind_sound A hA
      rw [kctxOf_cons] at ih
      exact Kinded.all ih
  | lam k' A, Λ, Δ, k, h => by
      change (inferKind Λ (k' :: Δ) A).map (Kind.arr k') = some k at h
      cases hA : inferKind Λ (k' :: Δ) A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          cases h
          have ih := inferKind_sound A hA
          rw [kctxOf_cons] at ih
          exact Kinded.lam ih
  | app k' A B, Λ, Δ, k, h => by
      obtain ⟨hA, hB⟩ := appK_inv (x := inferKind Λ Δ A) (y := inferKind Λ Δ B) h
      exact Kinded.app (inferKind_sound A hA) (inferKind_sound B hB)
  | kall0 A, Λ, Δ, k, h => by
      obtain ⟨hA, rfl⟩ := starK_inv (o := inferKind Λ (Δ.map Kind.sh₀) A) h
      have ih := inferKind_sound A hA
      rw [kctxOf_klift0] at ih
      exact Kinded.kall0 ih
  | kall1 A, Λ, Δ, k, h => by
      obtain ⟨hA, rfl⟩ := starK_inv (o := inferKind Λ (Δ.map Kind.sh₁) A) h
      have ih := inferKind_sound A hA
      rw [kctxOf_klift1] at ih
      exact Kinded.kall1 ih
  | pack k' A, Λ, Δ, k, h => by
      obtain ⟨hA, hk, rfl⟩ := packK_inv (x := inferKind Λ Δ A) h
      exact Kinded.pack (inferKind_sound A hA) hk
  | unpack k' A, Λ, Δ, k, h => by
      obtain ⟨hA, hk, rfl⟩ := unpackK_inv (x := inferKind Λ Δ A) h
      exact Kinded.unpack (inferKind_sound A hA) hk
  | apack l k' A, Λ, Δ, k, h => by
      obtain ⟨hA, hk, rfl⟩ := apackK_inv (x := inferKind Λ Δ A) h
      exact Kinded.apack (inferKind_sound A hA) hk
  | aunpack l k' A, Λ, Δ, k, h => by
      obtain ⟨hA, hk, rfl⟩ := aunpackK_inv (x := inferKind Λ Δ A) h
      exact Kinded.aunpack (inferKind_sound A hA) hk
  | lall l A, Λ, Δ, k, h => by
      obtain ⟨hA, rfl⟩ := starK_inv (o := inferKind (l :: Λ) (Δ.map Kind.lsh) A) h
      have ih := inferKind_sound A hA
      rw [kctxOf_llift] at ih
      exact Kinded.lall ih
  | llam l A, Λ, Δ, k, h => by
      obtain ⟨kA, k', hA, hk', rfl⟩ := llamK_inv (x := inferKind (l :: Λ) (Δ.map Kind.lsh) A) h
      have ih := inferKind_sound A hA
      rw [kctxOf_llift, Kind.unshift?_spec hk'] at ih
      exact Kinded.llam ih
  | lapp l A c, Λ, Δ, k, h => by
      obtain ⟨hA, hc⟩ := lappK_inv (x := inferKind Λ Δ A) h
      exact Kinded.lapp (inferKind_sound A hA) hc

end Inference

end BusyLean.FLV
