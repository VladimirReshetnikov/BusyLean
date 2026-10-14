import BusyLean.Independent.EpsilonHardy

/-!
# System T over Brouwer trees (proof infrastructure)

`TT` is a simply typed λ-calculus with numbers, Brouwer trees and their
recursors: `rec` (natural recursion) and `fold` (iteration over a tree, with
`fold z s l (lim f) = l (fun n => fold z s l (f n))`). Its semantics is
denotational (`eval`).

`epsProgram` is a closed `TT` program whose value is `Feps (Feps 42)`, the
ordinal rung (`eval_epsProgram`). It writes `+`, `·n`, `ω^·`, the towers, `ε₀`
and the Hardy hierarchy as folds and recursions, mirroring the definitions in
`EpsilonHardy.lean`. This file is used only in proofs: the ladder rung runs
the program after it is compiled to Church encodings (`TreeEmbedding.lean`).
-/

namespace BusyLean.Indep.TT

open BusyLean.Indep.Eps

inductive Ty where
  | nat : Ty
  | tree : Ty
  | arr : Ty → Ty → Ty

@[reducible] def den : Ty → Type
  | .nat => Nat
  | .tree => BTree
  | .arr a b => den a → den b

/-- Natural recursion: `recursion a f (n+1) = f n (recursion a f n)`. -/
def recursion {α : Type} (a : α) (f : Nat → α → α) : Nat → α
  | 0 => a
  | n + 1 => f n (recursion a f n)

/-- Iteration over a Brouwer tree. -/
def fold {α : Type} (z : α) (s : α → α) (l : (Nat → α) → α) : BTree → α
  | .zero => z
  | .succ t => s (fold z s l t)
  | .lim f => l fun n => fold z s l (f n)

inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {σ : Ty} : Var (σ :: Γ) σ
  | there {Γ : List Ty} {σ τ : Ty} : Var Γ σ → Var (τ :: Γ) σ

inductive Tm : List Ty → Ty → Type where
  | var {Γ : List Ty} {σ : Ty} : Var Γ σ → Tm Γ σ
  | lam {Γ : List Ty} {σ τ : Ty} : Tm (σ :: Γ) τ → Tm Γ (.arr σ τ)
  | app {Γ : List Ty} {σ τ : Ty} : Tm Γ (.arr σ τ) → Tm Γ σ → Tm Γ τ
  | zero {Γ : List Ty} : Tm Γ .nat
  | succ {Γ : List Ty} : Tm Γ (.arr .nat .nat)
  | nrec {Γ : List Ty} (r : Ty) : Tm Γ (.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)))
  | tzero {Γ : List Ty} : Tm Γ .tree
  | tsucc {Γ : List Ty} : Tm Γ (.arr .tree .tree)
  | tlim {Γ : List Ty} : Tm Γ (.arr (.arr .nat .tree) .tree)
  | fold {Γ : List Ty} (r : Ty) :
      Tm Γ (.arr r (.arr (.arr r r) (.arr (.arr (.arr .nat r) r) (.arr .tree r))))

abbrev Env (Γ : List Ty) : Type := (σ : Ty) → Var Γ σ → den σ

def Env.cons {Γ : List Ty} {σ : Ty} (x : den σ) (ρ : Env Γ) : Env (σ :: Γ)
  | _, .here => x
  | _, .there v => ρ _ v

def eval : {Γ : List Ty} → {σ : Ty} → Tm Γ σ → Env Γ → den σ
  | _, _, .var v, ρ => ρ _ v
  | _, _, .lam b, ρ => fun x => eval b (Env.cons x ρ)
  | _, _, .app s u, ρ => eval s ρ (eval u ρ)
  | _, _, .zero, _ => (0 : Nat)
  | _, _, .succ, _ => Nat.succ
  | _, _, .nrec _, _ => recursion
  | _, _, .tzero, _ => BTree.zero
  | _, _, .tsucc, _ => BTree.succ
  | _, _, .tlim, _ => BTree.lim
  | _, _, .fold _, _ => fold

def env0 : Env [] := fun _ v => nomatch v

/-! ## The program -/

section Program

variable {Γ : List Ty}

open Tm (var lam app zero succ nrec tzero tsucc tlim)

abbrev v0 {σ : Ty} : Tm (σ :: Γ) σ := .var .here
abbrev v1 {σ τ : Ty} : Tm (τ :: σ :: Γ) σ := .var (.there .here)
abbrev v2 {σ τ υ : Ty} : Tm (υ :: τ :: σ :: Γ) σ := .var (.there (.there .here))

/-- `a + b = fold a succ lim b`. -/
def addT : Tm Γ (.arr .tree (.arr .tree .tree)) :=
  lam (lam (app (app (app (app (Tm.fold .tree) v1) tsucc) tlim) v0))

/-- `a · i`. -/
def mulNatT : Tm Γ (.arr .tree (.arr .nat .tree)) :=
  lam (app (app (nrec .tree) tzero) (lam (lam (app (app addT v0) v2))))

/-- `ω^a`. -/
def opowT : Tm Γ (.arr .tree .tree) :=
  app (app (app (Tm.fold .tree) (app tsucc tzero))
      (lam (app tlim (app mulNatT v0))))
    tlim

def omegaT : Tm Γ .tree := app tlim (app mulNatT (app tsucc tzero))

def towerT : Tm Γ (.arr .nat .tree) :=
  app (app (nrec .tree) omegaT) (lam (lam (app opowT v0)))

def epsilon0T : Tm Γ .tree := app tlim towerT

/-- `pred`, `a - b`, `a + b` and `max a b` on numbers. -/
def predT : Tm Γ (.arr .nat .nat) := app (app (nrec .nat) zero) (lam (lam v1))

def subT : Tm Γ (.arr .nat (.arr .nat .nat)) :=
  lam (app (app (nrec .nat) v0) (lam (lam (app predT v0))))

def plusT : Tm Γ (.arr .nat (.arr .nat .nat)) :=
  lam (app (app (nrec .nat) v0) (lam (lam (app succ v0))))

def maxT : Tm Γ (.arr .nat (.arr .nat .nat)) :=
  lam (lam (app (app plusT v1) (app (app subT v0) v1)))

/-- `maxUpTo g y`. -/
def maxUpToT : Tm Γ (.arr (.arr .nat .nat) (.arr .nat .nat)) :=
  lam (app (app (nrec .nat) (app v0 zero))
    (lam (lam (app (app maxT v0) (app v2 (app succ v1))))))

/-- The Hardy hierarchy, by a fold at type `nat → nat`. -/
def hardyT : Tm Γ (.arr .tree (.arr .nat .nat)) :=
  app (app (app (Tm.fold (.arr .nat .nat)) (lam v0))
      (lam (lam (app v1 (app succ v0)))))
    (lam (lam (app (app maxUpToT (lam (app (app v2 v0) v1))) v0)))

def fepsT : Tm Γ (.arr .nat .nat) := app hardyT epsilon0T

def numT : Nat → Tm Γ .nat
  | 0 => zero
  | k + 1 => app succ (numT k)

/-- `Feps (Feps 42)` as a `TT` program. -/
def epsProgram : Tm [] .nat := app fepsT (app fepsT (numT 42))

end Program

/-! ## Its value -/

theorem fold_add (a : BTree) : ∀ b, fold a BTree.succ BTree.lim b = BTree.add a b
  | .zero => rfl
  | .succ b => congrArg BTree.succ (fold_add a b)
  | .lim f => congrArg BTree.lim (funext fun n => fold_add a (f n))

theorem eval_addT {Γ : List Ty} (ρ : Env Γ) (a b : BTree) :
    eval (addT : Tm Γ _) ρ a b = BTree.add a b := fold_add a b

theorem eval_mulNatT {Γ : List Ty} (ρ : Env Γ) (a : BTree) :
    ∀ i, eval (mulNatT : Tm Γ _) ρ a i = BTree.mulNat a i
  | 0 => rfl
  | i + 1 => by
      show eval (addT : Tm _ _) _ (eval (mulNatT : Tm Γ _) ρ a i) a = _
      rw [eval_addT, eval_mulNatT ρ a i]
      rfl

theorem fold_opow : ∀ a, fold (BTree.succ .zero) (fun p => BTree.lim (BTree.mulNat p)) BTree.lim a =
    BTree.opow a
  | .zero => rfl
  | .succ a => by
      show BTree.lim (BTree.mulNat (fold _ _ _ a)) = _
      rw [fold_opow a]; rfl
  | .lim f => congrArg BTree.lim (funext fun n => fold_opow (f n))

theorem eval_opowT {Γ : List Ty} (ρ : Env Γ) (a : BTree) :
    eval (opowT : Tm Γ _) ρ a = BTree.opow a := by
  have h : (fun p => BTree.lim (eval (mulNatT : Tm (.tree :: Γ) _) (Env.cons (σ := .tree) p ρ) p)) =
      fun p => BTree.lim (BTree.mulNat p) := by
    funext p; congr 1; funext i; exact eval_mulNatT _ p i
  show fold _ (fun p => BTree.lim (eval (mulNatT : Tm (.tree :: Γ) _) (Env.cons (σ := .tree) p ρ) p)) BTree.lim a = _
  rw [h]
  exact fold_opow a

theorem eval_omegaT {Γ : List Ty} (ρ : Env Γ) : (eval (omegaT : Tm Γ .tree) ρ : BTree) = BTree.omega := by
  show BTree.lim (eval (mulNatT : Tm Γ _) ρ (BTree.succ .zero)) = _
  congr 1; funext i; exact eval_mulNatT ρ _ i

theorem eval_towerT {Γ : List Ty} (ρ : Env Γ) : ∀ k, eval (towerT : Tm Γ _) ρ k = BTree.tower k
  | 0 => eval_omegaT ρ
  | k + 1 => by
      show eval (opowT : Tm _ _) _ (eval (towerT : Tm Γ _) ρ k) = _
      rw [eval_opowT, eval_towerT ρ k]
      rfl

theorem eval_epsilon0T {Γ : List Ty} (ρ : Env Γ) :
    (eval (epsilon0T : Tm Γ .tree) ρ : BTree) = BTree.epsilon0 := by
  show BTree.lim (eval (towerT : Tm Γ _) ρ) = _
  congr 1; funext k; exact eval_towerT ρ k

theorem eval_predT {Γ : List Ty} (ρ : Env Γ) : ∀ n, eval (predT : Tm Γ _) ρ n = Nat.pred n
  | 0 => rfl
  | _ + 1 => rfl

theorem eval_subT {Γ : List Ty} (ρ : Env Γ) (a : Nat) : ∀ b, eval (subT : Tm Γ _) ρ a b = a - b
  | 0 => rfl
  | b + 1 => by
      show eval (predT : Tm _ _) _ (eval (subT : Tm Γ _) ρ a b) = _
      rw [eval_predT, eval_subT ρ a b]
      exact (Nat.sub_succ a b).symm

theorem eval_plusT {Γ : List Ty} (ρ : Env Γ) (a : Nat) : ∀ b, eval (plusT : Tm Γ _) ρ a b = a + b
  | 0 => rfl
  | b + 1 => by
      show Nat.succ (eval (plusT : Tm Γ _) ρ a b) = _
      rw [eval_plusT ρ a b]; rfl

theorem eval_maxT {Γ : List Ty} (ρ : Env Γ) (a b : Nat) : eval (maxT : Tm Γ _) ρ a b = max a b := by
  have h1 := eval_subT (Env.cons (σ := .nat) b (Env.cons (σ := .nat) a ρ)) b a
  have h2 := eval_plusT (Env.cons (σ := .nat) b (Env.cons (σ := .nat) a ρ)) a (b - a)
  show eval (plusT : Tm _ _) _ a (eval (subT : Tm _ _) _ b a) = _
  rw [h1, h2]
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h]; exact Nat.add_sub_cancel' h
  · rw [Nat.max_eq_left h, Nat.sub_eq_zero_of_le h]; rfl

theorem eval_maxUpToT {Γ : List Ty} (ρ : Env Γ) (g : Nat → Nat) :
    ∀ y, eval (maxUpToT : Tm Γ _) ρ g y = maxUpTo g y
  | 0 => rfl
  | y + 1 => by
      show eval (maxT : Tm _ _) _ (eval (maxUpToT : Tm Γ _) ρ g y) (g (y + 1)) = _
      rw [eval_maxT, eval_maxUpToT ρ g y]
      rfl

theorem eval_hardyT {Γ : List Ty} (ρ : Env Γ) : ∀ (a : BTree) (y : Nat),
    eval (hardyT : Tm Γ _) ρ a y = hardy a y
  | .zero, _ => rfl
  | .succ a, y => eval_hardyT ρ a (y + 1)
  | .lim f, y => by
      show eval (maxUpToT : Tm _ _) _ (fun i => eval (hardyT : Tm Γ _) ρ (f i) y) y = _
      rw [eval_maxUpToT]
      show maxUpTo (fun i => eval (hardyT : Tm Γ _) ρ (f i) y) y = maxUpTo (fun i => hardy (f i) y) y
      congr 1
      funext i
      exact eval_hardyT ρ (f i) y

theorem eval_numT {Γ : List Ty} (ρ : Env Γ) : ∀ k, (eval (numT k : Tm Γ .nat) ρ : Nat) = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (eval_numT ρ k)

theorem eval_fepsT {Γ : List Ty} (ρ : Env Γ) (n : Nat) : eval (fepsT : Tm Γ _) ρ n = Feps n := by
  show eval (hardyT : Tm Γ _) ρ (eval (epsilon0T : Tm Γ _) ρ) n = Feps n
  rw [eval_hardyT, eval_epsilon0T]
  rfl

/-- **The program computes the ordinal rung.** (No `rw` on the goal: its
closing `rfl` could try to evaluate `Feps`.) -/
theorem eval_app {Γ : List Ty} {σ τ : Ty} (s : Tm Γ (.arr σ τ)) (u : Tm Γ σ) (ρ : Env Γ) :
    eval (.app s u) ρ = eval s ρ (eval u ρ) := rfl

theorem eval_epsProgram : eval epsProgram env0 = Feps (Feps 42) := by
  unfold epsProgram
  rw [eval_app, eval_app, eval_numT, eval_fepsT, eval_fepsT]

end BusyLean.Indep.TT
