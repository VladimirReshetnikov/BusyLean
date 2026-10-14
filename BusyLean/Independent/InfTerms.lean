import BusyLean.Contender5
import BusyLean.Independent.TreeOrder

/-!
# Infinitary typed λ-terms (Tait)

Intrinsically typed terms over Contender 5's types, with the numeral
constructors `zero` and `succ` and an **infinitary** case distinction
`case n br` of type `nat`: its value is the value of `br k` when `n` has value
`k`. Natural recursion is compiled into such case trees (`TtoInf.lean`), so
recursion needs no constant.

`ht t` is the height of the term tree, a Brouwer tree (`ω`-branching at `case`).
Renaming preserves heights, and substitution adds at most the height of the
substituted terms at the bottom (`ht_subst`).
-/

namespace BusyLean.Indep.Inf

open BusyLean.C5 (Ty den)
open BusyLean.Indep.Eps
open BusyLean.Indep.Eps.BTree (add)

inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {σ : Ty} : Var (σ :: Γ) σ
  | there {Γ : List Ty} {σ τ : Ty} : Var Γ σ → Var (τ :: Γ) σ

inductive Tm : List Ty → Ty → Type where
  | var {Γ : List Ty} {σ : Ty} : Var Γ σ → Tm Γ σ
  | lam {Γ : List Ty} {σ τ : Ty} : Tm (σ :: Γ) τ → Tm Γ (.arr σ τ)
  | app {Γ : List Ty} {σ τ : Ty} : Tm Γ (.arr σ τ) → Tm Γ σ → Tm Γ τ
  | zero {Γ : List Ty} : Tm Γ .nat
  | succ {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat
  | case {Γ : List Ty} : Tm Γ .nat → (Nat → Tm Γ .nat) → Tm Γ .nat

/-! ## Semantics -/

abbrev Env (Γ : List Ty) : Type := (σ : Ty) → Var Γ σ → den σ

def Env.cons {Γ : List Ty} {σ : Ty} (x : den σ) (ρ : Env Γ) : Env (σ :: Γ)
  | _, .here => x
  | _, .there v => ρ _ v

def eval : {Γ : List Ty} → {σ : Ty} → Tm Γ σ → Env Γ → den σ
  | _, _, .var v, ρ => ρ _ v
  | _, _, .lam b, ρ => fun x => eval b (Env.cons x ρ)
  | _, _, .app s u, ρ => eval s ρ (eval u ρ)
  | _, _, .zero, _ => (0 : Nat)
  | _, _, .succ t, ρ => Nat.succ (eval t ρ)
  | _, _, .case n br, ρ => eval (br (eval n ρ)) ρ

/-! ## Renaming and substitution -/

abbrev Ren (Γ Δ : List Ty) : Type := (σ : Ty) → Var Γ σ → Var Δ σ

def Ren.lift {Γ Δ : List Ty} {τ : Ty} (r : Ren Γ Δ) : Ren (τ :: Γ) (τ :: Δ)
  | _, .here => .here
  | _, .there v => .there (r _ v)

def rename : {Γ Δ : List Ty} → {σ : Ty} → Ren Γ Δ → Tm Γ σ → Tm Δ σ
  | _, _, _, r, .var v => .var (r _ v)
  | _, _, _, r, .lam b => .lam (rename r.lift b)
  | _, _, _, r, .app s u => .app (rename r s) (rename r u)
  | _, _, _, _, .zero => .zero
  | _, _, _, r, .succ t => .succ (rename r t)
  | _, _, _, r, .case n br => .case (rename r n) fun k => rename r (br k)

abbrev Sub (Γ Δ : List Ty) : Type := (σ : Ty) → Var Γ σ → Tm Δ σ

def Sub.lift {Γ Δ : List Ty} {τ : Ty} (s : Sub Γ Δ) : Sub (τ :: Γ) (τ :: Δ)
  | _, .here => .var .here
  | _, .there v => rename (fun _ w => .there w) (s _ v)

def subst : {Γ Δ : List Ty} → {σ : Ty} → Sub Γ Δ → Tm Γ σ → Tm Δ σ
  | _, _, _, s, .var v => s _ v
  | _, _, _, s, .lam b => .lam (subst s.lift b)
  | _, _, _, s, .app t u => .app (subst s t) (subst s u)
  | _, _, _, _, .zero => .zero
  | _, _, _, s, .succ t => .succ (subst s t)
  | _, _, _, s, .case n br => .case (subst s n) fun k => subst s (br k)

/-- Substitute `u` for the innermost variable. -/
def Sub.single {Γ : List Ty} {σ : Ty} (u : Tm Γ σ) : Sub (σ :: Γ) Γ
  | _, .here => u
  | _, .there v => .var v

def subst1 {Γ : List Ty} {σ τ : Ty} (b : Tm (σ :: Γ) τ) (u : Tm Γ σ) : Tm Γ τ :=
  subst (Sub.single u) b

theorem eval_rename : ∀ {Γ Δ : List Ty} {σ : Ty} (r : Ren Γ Δ) (t : Tm Γ σ) (ρ : Env Δ),
    eval (rename r t) ρ = eval t (fun τ v => ρ τ (r τ v))
  | _, _, _, r, .var v, ρ => rfl
  | _, _, _, r, .lam b, ρ => by
      funext x
      show eval (rename r.lift b) (Env.cons x ρ) = eval b (Env.cons x fun τ v => ρ τ (r τ v))
      rw [eval_rename]
      congr 1
      funext τ v
      cases v <;> rfl
  | _, _, _, r, .app s u, ρ => by
      show eval (rename r s) ρ (eval (rename r u) ρ) = _
      rw [eval_rename r s, eval_rename r u]; rfl
  | _, _, _, _, .zero, _ => rfl
  | _, _, _, r, .succ t, ρ => by
      show Nat.succ (eval (rename r t) ρ) = _
      rw [eval_rename r t]; rfl
  | _, _, _, r, .case n br, ρ => by
      show eval (rename r (br (eval (rename r n) ρ))) ρ = _
      rw [eval_rename r n, eval_rename r]; rfl

theorem eval_subst : ∀ {Γ Δ : List Ty} {σ : Ty} (s : Sub Γ Δ) (t : Tm Γ σ) (ρ : Env Δ),
    eval (subst s t) ρ = eval t (fun τ v => eval (s τ v) ρ)
  | _, _, _, s, .var v, ρ => rfl
  | _, _, _, s, .lam b, ρ => by
      funext x
      show eval (subst s.lift b) (Env.cons x ρ) = eval b (Env.cons x fun τ v => eval (s τ v) ρ)
      rw [eval_subst]
      congr 1
      funext τ v
      cases v with
      | here => rfl
      | there v =>
          show eval (rename (fun _ w => .there w) (s τ v)) (Env.cons x ρ) = eval (s τ v) ρ
          rw [eval_rename]
          rfl
  | _, _, _, s, .app t u, ρ => by
      show eval (subst s t) ρ (eval (subst s u) ρ) = _
      rw [eval_subst s t, eval_subst s u]; rfl
  | _, _, _, _, .zero, _ => rfl
  | _, _, _, s, .succ t, ρ => by
      show Nat.succ (eval (subst s t) ρ) = _
      rw [eval_subst s t]; rfl
  | _, _, _, s, .case n br, ρ => by
      show eval (subst s (br (eval (subst s n) ρ))) ρ = _
      rw [eval_subst s n, eval_subst s]; rfl

theorem eval_subst1 {Γ : List Ty} {σ τ : Ty} (b : Tm (σ :: Γ) τ) (u : Tm Γ σ) (ρ : Env Γ) :
    eval (subst1 b u) ρ = eval b (Env.cons (eval u ρ) ρ) := by
  unfold subst1
  rw [eval_subst]
  congr 1
  funext τ v
  cases v <;> rfl

/-! ## Heights -/

def ht : {Γ : List Ty} → {σ : Ty} → Tm Γ σ → BTree
  | _, _, .var _ => .zero
  | _, _, .lam b => .succ (ht b)
  | _, _, .app s u => .succ (join (ht s) (ht u))
  | _, _, .zero => .zero
  | _, _, .succ t => .succ (ht t)
  | _, _, .case n br => .succ (join (.lim fun k => ht (br k)) (ht n))

theorem ht_rename : ∀ {Γ Δ : List Ty} {σ : Ty} (r : Ren Γ Δ) (t : Tm Γ σ), ht (rename r t) = ht t
  | _, _, _, _, .var _ => rfl
  | _, _, _, r, .lam b => congrArg BTree.succ (ht_rename r.lift b)
  | _, _, _, r, .app s u => by
      show BTree.succ (join (ht (rename r s)) (ht (rename r u))) = _
      rw [ht_rename r s, ht_rename r u]; rfl
  | _, _, _, _, .zero => rfl
  | _, _, _, r, .succ t => congrArg BTree.succ (ht_rename r t)
  | _, _, _, r, .case n br => by
      show BTree.succ (join (.lim fun k => ht (rename r (br k))) (ht (rename r n))) = _
      rw [ht_rename r n]
      congr 3
      funext k
      exact ht_rename r (br k)

theorem add_join_le {n : Nat} (B a b : BTree) : Le n (join (add B a) (add B b)) (add B (join a b)) :=
  .lim fun i => by
    by_cases e : i = 0
    · subst e; exact Le.refl n _
    · show Le n (if i = 0 then add B a else add B b) (add B (if i = 0 then a else b))
      simp only [e, ite_false]; exact Le.refl n _

theorem ht_subst {n : Nat} : ∀ {Γ Δ : List Ty} {σ : Ty} (s : Sub Γ Δ) {B : BTree},
    (∀ τ v, Le n (ht (s τ v)) B) → ∀ t : Tm Γ σ, Le n (ht (subst s t)) (add B (ht t))
  | _, _, _, s, B, hs, .var v => hs _ v
  | Γ, _, .arr α _, s, B, hs, .lam b => by
      have hl : ∀ ρ (v : Var (α :: Γ) ρ), Le n (ht (Sub.lift (τ := α) s ρ v)) B := fun τ v => by
        cases v with
        | here => exact .zero B
        | there v =>
            show Le n (ht (rename _ (s τ v))) B
            rw [ht_rename]; exact hs τ v
      exact .succ (ht_subst s.lift hl b)
  | _, _, _, s, B, hs, .app t u =>
      .succ ((join_mono (ht_subst s hs t) (ht_subst s hs u)).trans (add_join_le B _ _))
  | _, _, _, _, B, _, .zero => .zero _
  | _, _, _, s, B, hs, .succ t => .succ (ht_subst s hs t)
  | _, _, _, s, B, hs, .case m br =>
      .succ ((join_mono (.lim fun k => ht_subst s hs (br k)) (ht_subst s hs m)).trans
        (by exact add_join_le B (.lim fun k => ht (br k)) (ht m)))

theorem ht_subst1 {n : Nat} {Γ : List Ty} {σ τ : Ty} (b : Tm (σ :: Γ) τ) (u : Tm Γ σ) :
    Le n (ht (subst1 b u)) (add (ht u) (ht b)) :=
  ht_subst _ (fun _ v => by
    cases v with
    | here => exact Le.refl n _
    | there v => exact .zero _) b

end BusyLean.Indep.Inf
