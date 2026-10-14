import BusyLean.Independent.Buchholz

/-!
# System T over Brouwer trees and Buchholz's level trees (proof infrastructure)

`TT` is a simply typed λ-calculus with numbers, Brouwer trees, the level trees
`lev m` of `Buchholz.lean` and their recursors: `rec` (natural recursion),
`fold` (iteration over a Brouwer tree, with
`fold z s l (lim f) = l (fun n => fold z s l (f n))`) and `lfold0`, `lfoldS m`
(iteration over a level tree, with `lfold z s l p (sup μ f) = p μ (fun x => lfold z s l p (f x))`).
Its semantics is denotational (`eval`).

`epsProgram` is a closed `TT` program whose value is `Feps (Feps 42)`
(`eval_epsProgram`), and `buchProgram` one whose value is `F3 (F3 42)`, the
ordinal rung (`eval_buchProgram`). They write `+`, `·n`, `ω^·`, the towers,
`ε₀`, lifting and projecting between levels, `Ω_ν`, Buchholz's collapse and
the Hardy hierarchy as folds and recursions, mirroring `EpsilonHardy.lean` and
`Buchholz.lean`. This file is used only in proofs: the ladder rung runs the
programs after they are compiled to Church encodings (`TreeEmbedding.lean`).
-/

namespace BusyLean.Indep.TT

open BusyLean.Indep.Eps

inductive Ty where
  | nat : Ty
  | tree : Ty
  | lev : Nat → Ty
  | arr : Ty → Ty → Ty

@[reducible] def den : Ty → Type
  | .nat => Nat
  | .tree => BTree
  | .lev m => Buch.T m
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

/-- Iteration over a level tree. -/
def lfold {A α : Type} (z : α) (s : α → α) (l : (Nat → α) → α) (p : Nat → (A → α) → α) :
    Buch.Tr A → α
  | .zero => z
  | .succ t => s (lfold z s l p t)
  | .lim f => l fun n => lfold z s l p (f n)
  | .sup μ f => p μ fun x => lfold z s l p (f x)

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
  | lzero {Γ : List Ty} (m : Nat) : Tm Γ (.lev m)
  | lsucc {Γ : List Ty} (m : Nat) : Tm Γ (.arr (.lev m) (.lev m))
  | llim {Γ : List Ty} (m : Nat) : Tm Γ (.arr (.arr .nat (.lev m)) (.lev m))
  | lsup {Γ : List Ty} (m : Nat) :
      Tm Γ (.arr .nat (.arr (.arr (.lev m) (.lev (m + 1))) (.lev (m + 1))))
  | lfold0 {Γ : List Ty} (r : Ty) :
      Tm Γ (.arr r (.arr (.arr r r) (.arr (.arr (.arr .nat r) r)
        (.arr (.arr .nat (.arr (.arr .nat r) r)) (.arr (.lev 0) r)))))
  | lfoldS {Γ : List Ty} (m : Nat) (r : Ty) :
      Tm Γ (.arr r (.arr (.arr r r) (.arr (.arr (.arr .nat r) r)
        (.arr (.arr .nat (.arr (.arr (.lev m) r) r)) (.arr (.lev (m + 1)) r)))))

/-- The de Bruijn index of a variable. -/
def Var.idx : {Γ : List Ty} → {σ : Ty} → Var Γ σ → Nat
  | _, _, .here => 0
  | _, _, .there v => v.idx + 1

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
  | _, _, .lzero _, _ => Buch.Tr.zero
  | _, _, .lsucc _, _ => Buch.Tr.succ
  | _, _, .llim _, _ => Buch.Tr.lim
  | _, _, .lsup _, _ => Buch.Tr.sup
  | _, _, .lfold0 _, _ => lfold
  | _, _, .lfoldS _ _, _ => lfold

def env0 : Env [] := fun _ v => nomatch v

/-! ## The program -/

section Program

variable {Γ : List Ty}

open Tm (var lam app zero succ nrec tzero tsucc tlim)

abbrev v0 {σ : Ty} : Tm (σ :: Γ) σ := .var .here
abbrev v1 {σ τ : Ty} : Tm (τ :: σ :: Γ) σ := .var (.there .here)
abbrev v2 {σ τ υ : Ty} : Tm (υ :: τ :: σ :: Γ) σ := .var (.there (.there .here))
abbrev v3 {σ τ υ χ : Ty} : Tm (χ :: υ :: τ :: σ :: Γ) σ := .var (.there (.there (.there .here)))

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

/-! ### Buchholz's collapse -/

open Tm (lzero lsucc llim lsup)

abbrev v4 {σ τ υ χ ψ : Ty} : Tm (ψ :: χ :: υ :: τ :: σ :: Γ) σ :=
  .var (.there (.there (.there (.there .here))))
abbrev v5 {σ τ υ χ ψ ω : Ty} : Tm (ω :: ψ :: χ :: υ :: τ :: σ :: Γ) σ :=
  .var (.there (.there (.there (.there (.there .here)))))

/-- `λ a _ _. a`. -/
def kT {r : Ty} : Tm Γ (.arr r (.arr .nat (.arr r r))) := lam (lam (lam v2))

/-- `if μ < c then a else b`, as `rec b (λ _ _. a) (c - μ)`. -/
def ifLtT {r : Ty} (μ c : Tm Γ .nat) (a b : Tm Γ r) : Tm Γ r :=
  app (app (app (nrec r) b) (app kT a)) (app (app subT c) μ)

/-- `lfoldS m r z s l p`. -/
def foldS (m : Nat) {r : Ty} (z : Tm Γ r) (s : Tm Γ (.arr r r)) (l : Tm Γ (.arr (.arr .nat r) r))
    (p : Tm Γ (.arr .nat (.arr (.arr (.lev m) r) r))) : Tm Γ (.arr (.lev (m + 1)) r) :=
  app (app (app (app (Tm.lfoldS m r) z) s) l) p

/-- Lifting from level `m` to level `m + 1`, and projecting back. -/
structure LP (m : Nat) where
  lift : {Γ : List Ty} → Tm Γ (.arr (.lev m) (.lev (m + 1)))
  proj : {Γ : List Ty} → Tm Γ (.arr (.lev (m + 1)) (.lev m))

def lp0 : LP 0 where
  lift := app (app (app (app (Tm.lfold0 (.lev 1)) (lzero 1)) (lsucc 1)) (llim 1))
    (lam (lam (lzero 1)))
  proj := foldS 0 (lzero 0) (lsucc 0) (llim 0) (lam (lam (lzero 0)))

def lpStep (m : Nat) (r : LP m) : LP (m + 1) where
  lift := foldS m (lzero (m + 2)) (lsucc (m + 2)) (llim (m + 2))
    (lam (lam (ifLtT v1 (numT (m + 1))
      (app (app (lsup (m + 1)) v1) (lam (app v1 (app r.proj v0)))) (lzero (m + 2)))))
  proj := foldS (m + 1) (lzero (m + 1)) (lsucc (m + 1)) (llim (m + 1))
    (lam (lam (ifLtT v1 (numT (m + 1))
      (app (app (lsup m) v1) (lam (app v1 (app r.lift v0)))) (lzero (m + 1)))))

/-- All levels, by a single (non-mutual) recursion. -/
def lpT : (m : Nat) → LP m
  | 0 => lp0
  | m + 1 => lpStep m (lpT m)

def liftTm (m : Nat) {Γ : List Ty} : Tm Γ (.arr (.lev m) (.lev (m + 1))) :=
  (lpT m).lift

def projTm (m : Nat) {Γ : List Ty} : Tm Γ (.arr (.lev (m + 1)) (.lev m)) :=
  (lpT m).proj

/-- `a + b` at level `m + 1`. -/
def addL (m : Nat) : Tm Γ (.arr (.lev (m + 1)) (.arr (.lev (m + 1)) (.lev (m + 1)))) :=
  lam (lam (app (foldS m v1 (lsucc (m + 1)) (llim (m + 1)) (lam (lam (app (app (lsup m) v1) v0))))
    v0))

/-- `a · k` at level `m + 1`. -/
def mulNatL (m : Nat) : Tm Γ (.arr (.lev (m + 1)) (.arr .nat (.lev (m + 1)))) :=
  lam (app (app (nrec (.lev (m + 1))) (lzero (m + 1))) (lam (lam (app (app (addL m) v0) v2))))

/-- `a · c` at level `m + 1`. -/
def mulL (m : Nat) : Tm Γ (.arr (.lev (m + 1)) (.arr (.lev (m + 1)) (.lev (m + 1)))) :=
  lam (lam (app (foldS m (lzero (m + 1)) (lam (app (app (addL m) v0) v2)) (llim (m + 1))
    (lam (lam (app (app (lsup m) v1) v0)))) v0))

/-- `Ω_ν` at level `n + 1`. -/
def omegaTm (n : Nat) : Tm Γ (.arr .nat (.lev (n + 1))) :=
  app (app (nrec (.lev (n + 1))) (app (lsucc (n + 1)) (lzero (n + 1))))
    (lam (lam (app (app (lsup n) v1) (liftTm n))))

/-- Buchholz's collapse: `ψ_ν(α)` at level `n + 1` for `α` at level `n + 2`. -/
def psiTm (n : Nat) : Tm Γ (.arr (.lev (n + 2)) (.arr .nat (.lev (n + 1)))) :=
  foldS (n + 1) (omegaTm n)
    (lam (lam (app (llim (n + 1)) (lam (app (app (mulNatL n) (app v2 v1)) v0)))))
    (lam (lam (app (llim (n + 1)) (lam (app (app v2 v0) v1)))))
    (lam (lam (lam (ifLtT v2 v0
      (app (app (lsup n) v2) (lam (app (app v2 (app (liftTm n) v0)) v1)))
      (app (llim (n + 1)) (lam (app (app v2
        (app (app (app (nrec (.lev (n + 1))) (app (omegaTm n) v3)) (lam (lam (app (app v4 v0) v5))))
          v0)) v1)))))))

/-- `Ω_{n+2}^a` at level `n + 2`. -/
def opowTopTm (n : Nat) : Tm Γ (.arr (.lev (n + 2)) (.lev (n + 2))) :=
  foldS (n + 1) (app (lsucc (n + 2)) (lzero (n + 2)))
    (lam (app (app (lsup (n + 1)) (numT (n + 1)))
      (lam (app (app (mulL (n + 1)) v1) (app (liftTm (n + 1)) v0)))))
    (llim (n + 2))
    (lam (lam (app (app (lsup (n + 1)) v1) v0)))

def towerTopTm (n : Nat) : Tm Γ (.arr .nat (.lev (n + 2))) :=
  app (app (nrec (.lev (n + 2))) (app (liftTm (n + 1)) (app (omegaTm n) (numT 1))))
    (lam (lam (app (opowTopTm n) v0)))

def epsTopTm (n : Nat) : Tm Γ (.lev (n + 2)) := app (llim (n + 2)) (towerTopTm n)

/-- The Brouwer tree of a tree of level `n + 1`. -/
def toBTm (n : Nat) : Tm Γ (.arr (.lev (n + 1)) .tree) :=
  foldS n tzero tsucc tlim (lam (lam tzero))

def thetaTm (n : Nat) : Tm Γ .tree := app (toBTm n) (app (app (psiTm n) (epsTopTm n)) zero)

def f3T : Tm Γ (.arr .nat .nat) := app hardyT (thetaTm 40)

/-- `F3 (F3 42)` as a `TT` program. -/
def buchProgram : Tm [] .nat := app f3T (app f3T (numT 42))

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

/-! ## The value of `buchProgram` -/

section Buchholz

open Buch (Tr)

theorem recursion_lt {α : Type} (a b : α) (μ c : Nat) :
    recursion b (fun _ _ => a) (c - μ) = if μ < c then a else b := by
  by_cases h : μ < c
  · obtain ⟨k, hk⟩ : ∃ k, c - μ = k + 1 := ⟨c - μ - 1, by omega⟩
    rw [hk]
    show a = if μ < c then a else b
    simp only [h, ite_true]
  · rw [show c - μ = 0 by omega]
    show b = if μ < c then a else b
    simp only [h, ite_false]

theorem eval_ifLtT {Γ : List Ty} {r : Ty} (μ c : Tm Γ .nat) (a b : Tm Γ r) (ρ : Env Γ) :
    eval (ifLtT μ c a b) ρ = if eval μ ρ < eval c ρ then eval a ρ else eval b ρ := by
  show recursion (eval b ρ) (fun _ _ => eval a ρ) (eval (subT : Tm Γ _) ρ (eval c ρ) (eval μ ρ)) = _
  rw [eval_subT]
  exact recursion_lt _ _ _ _

theorem lfold_cmap {A B : Type} (thr : Nat) (h : B → A) : ∀ x : Tr A,
    lfold Tr.zero Tr.succ Tr.lim (fun μ rs => if μ < thr then Tr.sup μ (fun y => rs (h y)) else Tr.zero)
      x = Tr.cmap thr h x
  | .zero => rfl
  | .succ a => congrArg Tr.succ (lfold_cmap thr h a)
  | .lim f => congrArg Tr.lim (funext fun i => lfold_cmap thr h (f i))
  | .sup μ f => by
      show (if μ < thr then Tr.sup μ (fun y => lfold _ _ _ _ (f (h y))) else Tr.zero) =
        (if μ < thr then Tr.sup μ (fun y => Tr.cmap thr h (f (h y))) else Tr.zero)
      have e : (fun y => lfold Tr.zero Tr.succ Tr.lim
          (fun μ rs => if μ < thr then Tr.sup μ (fun y => rs (h y)) else Tr.zero) (f (h y))) =
          fun y => Tr.cmap thr h (f (h y)) := funext fun y => lfold_cmap thr h (f (h y))
      rw [e]

theorem lfold_cmap0 {A B : Type} (h : B → A) (x : Tr A) :
    lfold Tr.zero Tr.succ Tr.lim (fun _ _ => Tr.zero) x = Tr.cmap 0 h x := by
  rw [← lfold_cmap]
  congr 1

theorem eval_lp : ∀ (m : Nat) {Γ : List Ty} (ρ : Env Γ),
    eval (liftTm m : Tm Γ _) ρ = Buch.lift m ∧ eval (projTm m : Tm Γ _) ρ = Buch.proj m
  | 0, _, _ => ⟨funext fun x => by
      show lfold Tr.zero Tr.succ Tr.lim (fun _ _ => Tr.zero) x = Tr.cmap 0 _ x
      exact lfold_cmap0 _ x,
    funext fun x => by
      show lfold Tr.zero Tr.succ Tr.lim (fun _ _ => Tr.zero) x = Tr.cmap 0 _ x
      exact lfold_cmap0 _ x⟩
  | m + 1, Γ, ρ => by
      constructor
      · funext x
        refine (congrArg (fun (p : Nat → (Buch.T m → Buch.T (m + 2)) → Buch.T (m + 2)) =>
          lfold Tr.zero Tr.succ Tr.lim p x) ?_).trans (lfold_cmap (m + 1) (Buch.proj m) x)
        funext μ rs
        refine (eval_ifLtT _ _ _ _ _).trans ?_
        rw [eval_numT]
        show (if μ < m + 1 then Tr.sup μ (fun y => rs (eval (projTm m) _ y)) else Tr.zero) = _
        simp only [(eval_lp m _).2]
        try rfl
      · funext x
        refine (congrArg (fun (p : Nat → (Buch.T (m + 1) → Buch.T (m + 1)) → Buch.T (m + 1)) =>
          lfold Tr.zero Tr.succ Tr.lim p x) ?_).trans (lfold_cmap (m + 1) (Buch.lift m) x)
        funext μ rs
        refine (eval_ifLtT _ _ _ _ _).trans ?_
        rw [eval_numT]
        show (if μ < m + 1 then Tr.sup μ (fun y => rs (eval (liftTm m) _ y)) else Tr.zero) = _
        simp only [(eval_lp m _).1]
        try rfl

theorem eval_liftTm (m : Nat) {Γ : List Ty} (ρ : Env Γ) :
    eval (liftTm m : Tm Γ _) ρ = Buch.lift m := (eval_lp m ρ).1

theorem lfold_add {A : Type} (a : Tr A) : ∀ b : Tr A,
    lfold a Tr.succ Tr.lim (fun μ rs => Tr.sup μ rs) b = Tr.add a b
  | .zero => rfl
  | .succ b => congrArg Tr.succ (lfold_add a b)
  | .lim f => congrArg Tr.lim (funext fun i => lfold_add a (f i))
  | .sup μ f => congrArg (Tr.sup μ) (funext fun x => lfold_add a (f x))

theorem eval_addL (m : Nat) {Γ : List Ty} (ρ : Env Γ) (a b : Buch.T (m + 1)) :
    eval (addL m : Tm Γ _) ρ a b = Tr.add a b := lfold_add a b

theorem eval_mulNatL (m : Nat) {Γ : List Ty} (ρ : Env Γ) (a : Buch.T (m + 1)) :
    ∀ k, eval (mulNatL m : Tm Γ _) ρ a k = Tr.mulNat a k
  | 0 => rfl
  | k + 1 => by
      show eval (addL m : Tm _ _) _ (eval (mulNatL m : Tm Γ _) ρ a k) a = _
      rw [eval_addL, eval_mulNatL m ρ a k]
      rfl

theorem lfold_mul {A : Type} (a : Tr A) : ∀ b : Tr A,
    lfold Tr.zero (fun x => Tr.add x a) Tr.lim (fun μ rs => Tr.sup μ rs) b = Tr.mul a b
  | .zero => rfl
  | .succ b => congrArg (fun x => Tr.add x a) (lfold_mul a b)
  | .lim f => congrArg Tr.lim (funext fun i => lfold_mul a (f i))
  | .sup μ f => congrArg (Tr.sup μ) (funext fun x => lfold_mul a (f x))

theorem eval_mulL (m : Nat) {Γ : List Ty} (ρ : Env Γ) (a b : Buch.T (m + 1)) :
    eval (mulL m : Tm Γ _) ρ a b = Tr.mul a b := by
  rw [← lfold_mul]
  show lfold Tr.zero _ Tr.lim _ b = _
  congr 1
  funext x
  exact eval_addL m _ x a

theorem eval_omegaTm (n : Nat) {Γ : List Ty} (ρ : Env Γ) :
    eval (omegaTm n : Tm Γ _) ρ = Buch.omega (n + 1) := by
  funext ν
  cases ν with
  | zero => rfl
  | succ ν =>
      show Tr.sup ν (eval (liftTm n : Tm _ _) _) = Tr.sup ν fun y => Buch.lift n y
      rw [eval_liftTm]

theorem recursion_iterate {α : Type} (g : α → α) (b : α) :
    ∀ m, recursion b (fun _ x => g x) m = Buch.iterate g m b
  | 0 => rfl
  | m + 1 => congrArg g (recursion_iterate g b m)

theorem lfold_psi (n : Nat) : ∀ a : Buch.T (n + 2),
    lfold (Buch.omega (n + 1))
      (fun r ν => Tr.lim fun k => Tr.mulNat (r ν) k)
      (fun rs ν => Tr.lim fun k => rs k ν)
      (fun μ rs ν => if μ < ν then Tr.sup μ (fun y => rs (Buch.lift n y) ν)
        else Tr.lim fun k => rs (Buch.iterate (fun g => rs g μ) k (Buch.omega (n + 1) μ)) ν) a =
      Buch.psiAll (n + 1) a
  | .zero => rfl
  | .succ a => by
      funext ν
      show Tr.lim (fun k => Tr.mulNat (lfold (α := Nat → Buch.T (n + 1)) _ _ _ _ a ν) k) = _
      rw [lfold_psi n a]; rfl
  | .lim f => by
      funext ν
      show Tr.lim (fun k => lfold (α := Nat → Buch.T (n + 1)) _ _ _ _ (f k) ν) =
        Tr.lim fun k => Buch.psiAll (n + 1) (f k) ν
      congr 1; funext k; rw [lfold_psi n (f k)]
  | .sup μ f => by
      funext ν
      have e : ∀ x, lfold (Buch.omega (n + 1))
          (fun r ν => Tr.lim fun k => Tr.mulNat (r ν) k)
          (fun rs ν => Tr.lim fun k => rs k ν)
          (fun μ rs ν => if μ < ν then Tr.sup μ (fun y => rs (Buch.lift n y) ν)
            else Tr.lim fun k => rs (Buch.iterate (fun g => rs g μ) k (Buch.omega (n + 1) μ)) ν)
          (f x) = Buch.psiAll (n + 1) (f x) := fun x => lfold_psi n (f x)
      show (if μ < ν then Tr.sup μ (fun y =>
        lfold (α := Nat → Buch.T (n + 1)) _ _ _ _ (f (Buch.lift n y)) ν) else _) = _
      simp only [e]
      rfl

theorem eval_psiTm (n : Nat) {Γ : List Ty} (ρ : Env Γ) :
    eval (psiTm n : Tm Γ _) ρ = Buch.psiAll (n + 1) := by
  funext a
  rw [← lfold_psi n a]
  show lfold (eval (omegaTm n : Tm Γ _) ρ) _ _ _ a = _
  rw [eval_omegaTm]
  congr 1
  · funext r ν
    show Tr.lim (fun k => eval (mulNatL n : Tm _ _) _ (r ν) k) = _
    congr 1; funext k; exact eval_mulNatL n _ (r ν) k
  · funext μ rs ν
    refine (eval_ifLtT _ _ _ _ _).trans ?_
    show (if μ < ν then Tr.sup μ (fun y => rs (eval (liftTm n : Tm _ _) _ y) ν)
      else Tr.lim fun k => rs (recursion (eval (omegaTm n : Tm _ _) _ μ) (fun _ g => rs g μ) k) ν) = _
    simp only [eval_liftTm, eval_omegaTm, recursion_iterate]

theorem lfold_opowTop (n : Nat) : ∀ a : Buch.T (n + 2),
    lfold (Tr.succ Tr.zero) (fun x => Tr.sup (n + 1) fun b => Tr.mul x (Buch.lift (n + 1) b)) Tr.lim
      (fun μ rs => Tr.sup μ rs) a = Buch.opowTop (n + 1) a
  | .zero => rfl
  | .succ a => by
      show Tr.sup (n + 1) (fun b => Tr.mul (lfold _ _ _ _ a) (Buch.lift (n + 1) b)) = _
      rw [lfold_opowTop n a]; rfl
  | .lim f => congrArg Tr.lim (funext fun i => lfold_opowTop n (f i))
  | .sup μ f => congrArg (Tr.sup μ) (funext fun x => lfold_opowTop n (f x))

theorem eval_opowTopTm (n : Nat) {Γ : List Ty} (ρ : Env Γ) :
    eval (opowTopTm n : Tm Γ _) ρ = Buch.opowTop (n + 1) := by
  funext a
  rw [← lfold_opowTop n a]
  show lfold _ _ Tr.lim _ a = _
  congr 1
  funext x
  show Tr.sup (eval (numT (n + 1) : Tm _ .nat) _)
    (fun b => eval (mulL (n + 1) : Tm _ _) _ x (eval (liftTm (n + 1) : Tm _ _) _ b)) = _
  simp only [eval_numT, eval_mulL, eval_liftTm]

theorem eval_towerTopTm (n : Nat) {Γ : List Ty} (ρ : Env Γ) :
    ∀ k, eval (towerTopTm n : Tm Γ _) ρ k = Buch.towerTop (n + 1) k
  | 0 => by
      show eval (liftTm (n + 1) : Tm Γ _) ρ (eval (omegaTm n : Tm Γ _) ρ (eval (numT 1 : Tm Γ _) ρ)) = _
      rw [eval_liftTm, eval_omegaTm, eval_numT]
      rfl
  | k + 1 => by
      show eval (opowTopTm n : Tm _ _) _ (eval (towerTopTm n : Tm Γ _) ρ k) = _
      rw [eval_opowTopTm, eval_towerTopTm n ρ k]
      rfl

theorem eval_epsTopTm (n : Nat) {Γ : List Ty} (ρ : Env Γ) :
    (eval (epsTopTm n : Tm Γ _) ρ : Buch.T (n + 2)) = Buch.epsTop (n + 1) := by
  show Tr.lim (eval (towerTopTm n : Tm Γ _) ρ) = _
  congr 1; funext k; exact eval_towerTopTm n ρ k

theorem lfold_toB {A : Type} : ∀ x : Tr A,
    lfold Eps.BTree.zero Eps.BTree.succ Eps.BTree.lim (fun _ _ => Eps.BTree.zero) x = Tr.toB x
  | .zero => rfl
  | .succ a => congrArg Eps.BTree.succ (lfold_toB a)
  | .lim f => congrArg Eps.BTree.lim (funext fun i => lfold_toB (f i))
  | .sup _ _ => rfl

theorem eval_thetaTm (n : Nat) {Γ : List Ty} (ρ : Env Γ) :
    (eval (thetaTm n : Tm Γ .tree) ρ : BTree) = Buch.theta (n + 1) := by
  show lfold _ _ _ _ (eval (psiTm n : Tm Γ _) ρ (eval (epsTopTm n : Tm Γ _) ρ) 0) = _
  rw [eval_psiTm, eval_epsTopTm]
  exact lfold_toB _

theorem eval_f3T {Γ : List Ty} (ρ : Env Γ) (x : Nat) : eval (f3T : Tm Γ _) ρ x = F3 x := by
  show eval (hardyT : Tm Γ _) ρ (eval (thetaTm 40 : Tm Γ _) ρ) x = F3 x
  rw [eval_hardyT, eval_thetaTm]
  rfl

theorem eval_buchProgram : eval buchProgram env0 = F3 (F3 42) := by
  unfold buchProgram
  rw [eval_app, eval_app, eval_numT, eval_f3T, eval_f3T]

end Buchholz

end BusyLean.Indep.TT
