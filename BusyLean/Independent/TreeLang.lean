import BusyLean.Independent.Buchholz

/-!
# System T over Brouwer trees and Buchholz's level trees (proof infrastructure)

`TT` is a simply typed λ-calculus with numbers, Brouwer trees, the level trees
`lev m` of `Buchholz.lean` and their recursors: `rec` (natural recursion),
`fold` (iteration over a Brouwer tree, with
`fold z s l (lim f) = l (fun n => fold z s l (f n))`) and `lfold0`, `lfoldS m`
(iteration over a level tree, with `lfold z s l p (sup μ f) = p μ (fun x => lfold z s l p (f x))`).
Its semantics is denotational (`eval`).

The pieces of the ordinal rung that live at a single level are closed `TT`
terms whose levels occur only in their types: conversions between levels
(`cmapT`, `dropT`, `raiseT`), arithmetic (`addL`, `mulNatL`, `add0T`,
`mulNat0T`), `if μ < c` (`ifLtC`), the `sup`s of level `0` (`supVia0T`) and the
Brouwer tree of a tree of level `0` (`toB0T`). `tfbShell = λθ. H_θ(H_θ(42))` is
the rung as a function of its ordinal (`eval_tfbShell`). This file is used only
in proofs: the ladder rung runs the pieces after they are translated to
Church encodings in Fω (`TFBProg.lean`), and the logical relation of
`TreeEmbedding.lean` gives their meaning at every level.
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
  | lsup0 {Γ : List Ty} : Tm Γ (.arr .nat (.arr (.arr .nat (.lev 0)) (.lev 0)))
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
  | _, _, .lsup0, _ => Buch.Tr.sup
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

def numT : Nat → Tm Γ .nat
  | 0 => zero
  | k + 1 => app succ (numT k)

/-! ### Level trees

The levels occur only in the types, so the untyped translation of each piece
is the same at every level. -/

open Tm (lzero lsucc llim lsup)

/-- `λ a _ _. a`. -/
def kT {r : Ty} : Tm Γ (.arr r (.arr .nat (.arr r r))) := lam (lam (lam v2))

/-- `if μ < c then a else b`, as `rec b (λ _ _. a) (c - μ)`. -/
def ifLtT {r : Ty} (μ c : Tm Γ .nat) (a b : Tm Γ r) : Tm Γ r :=
  app (app (app (nrec r) b) (app kT a)) (app (app subT c) μ)

/-- `lfoldS m r z s l p`. -/
def foldS (m : Nat) {r : Ty} (z : Tm Γ r) (s : Tm Γ (.arr r r)) (l : Tm Γ (.arr (.arr .nat r) r))
    (p : Tm Γ (.arr .nat (.arr (.arr (.lev m) r) r))) : Tm Γ (.arr (.lev (m + 1)) r) :=
  app (app (app (app (Tm.lfoldS m r) z) s) l) p

/-- `a + b` at level `m + 1`. -/
def addL (m : Nat) : Tm Γ (.arr (.lev (m + 1)) (.arr (.lev (m + 1)) (.lev (m + 1)))) :=
  lam (lam (app (foldS m v1 (lsucc (m + 1)) (llim (m + 1)) (lam (lam (app (app (lsup m) v1) v0))))
    v0))

/-- `a · k` at level `m + 1`. -/
def mulNatL (m : Nat) : Tm Γ (.arr (.lev (m + 1)) (.arr .nat (.lev (m + 1)))) :=
  lam (app (app (nrec (.lev (m + 1))) (lzero (m + 1))) (lam (lam (app (app (addL m) v0) v2))))

/-! ### Conversions between levels, and the rung -/

/-- `λ thr h. cmap thr h`: from level `a + 1` to level `b + 1`, converting the
branches with `h` and keeping the `sup`s of level `< thr`. -/
def cmapT (a b : Nat) :
    Tm Γ (.arr .nat (.arr (.arr (.lev b) (.lev a)) (.arr (.lev (a + 1)) (.lev (b + 1))))) :=
  lam (lam (foldS a (lzero (b + 1)) (lsucc (b + 1)) (llim (b + 1))
    (lam (lam (ifLtT v1 v3 (app (app (lsup b) v1) (lam (app v1 (app v3 v0)))) (lzero (b + 1)))))))

/-- From level `a + 1` to level `0`, dropping every `sup`. -/
def dropT (a : Nat) : Tm Γ (.arr (.lev (a + 1)) (.lev 0)) :=
  foldS a (lzero 0) (lsucc 0) (llim 0) (lam (lam (lzero 0)))

/-- From level `0` to level `b`, dropping every `sup`. -/
def raiseT (b : Nat) : Tm Γ (.arr (.lev 0) (.lev b)) :=
  app (app (app (app (Tm.lfold0 (.lev b)) (lzero b)) (lsucc b)) (llim b)) (lam (lam (lzero b)))

/-- `a + b` at level `0`. -/
def add0T : Tm Γ (.arr (.lev 0) (.arr (.lev 0) (.lev 0))) :=
  lam (lam (app (app (app (app (app (Tm.lfold0 (.lev 0)) v1) (lsucc 0)) (llim 0))
    (lam (lam (app (app Tm.lsup0 v1) v0)))) v0))

/-- `λ μ. sup μ (λ _. 0)` at level `0`. -/
def supVia0T : Tm Γ (.arr .nat (.lev 0)) := lam (app (app Tm.lsup0 v0) (lam (lzero 0)))

/-- `a · k` at level `0`. -/
def mulNat0T : Tm Γ (.arr (.lev 0) (.arr .nat (.lev 0))) :=
  lam (app (app (nrec (.lev 0)) (lzero 0)) (lam (lam (app (app add0T v0) v2))))

/-- `λ μ c a b. if μ < c then a else b`. -/
def ifLtC {r : Ty} : Tm Γ (.arr .nat (.arr .nat (.arr r (.arr r r)))) :=
  lam (lam (lam (lam (ifLtT v3 v2 v1 v0))))

/-- The Brouwer tree of a tree of level `0`. -/
def toB0T : Tm Γ (.arr (.lev 0) .tree) :=
  app (app (app (app (Tm.lfold0 .tree) tzero) tsucc) tlim) (lam (lam tzero))

/-- `λ θ. H_θ(H_θ(42))`: the rung, given its ordinal as a tree. -/
def tfbShell : Tm [] (.arr .tree .nat) :=
  lam (app (app hardyT v0) (app (app hardyT v0) (numT 42)))

end Program

/-! ## Its value -/

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

/-! ## The values of the pieces on level trees -/

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

theorem recursion_iterate {α : Type} (g : α → α) (b : α) :
    ∀ m, recursion b (fun _ x => g x) m = Buch.iterate g m b
  | 0 => rfl
  | m + 1 => congrArg g (recursion_iterate g b m)

theorem lfold_toB {A : Type} : ∀ x : Tr A,
    lfold Eps.BTree.zero Eps.BTree.succ Eps.BTree.lim (fun _ _ => Eps.BTree.zero) x = Tr.toB x
  | .zero => rfl
  | .succ a => congrArg Eps.BTree.succ (lfold_toB a)
  | .lim f => congrArg Eps.BTree.lim (funext fun i => lfold_toB (f i))
  | .sup _ _ => rfl

theorem eval_cmapT (a b : Nat) {Γ : List Ty} (ρ : Env Γ) (thr : Nat) (h : Buch.T b → Buch.T a) :
    eval (cmapT a b : Tm Γ _) ρ thr h = Tr.cmap thr h := by
  funext x
  refine (congrArg (fun (q : Nat → (Buch.T a → Buch.T (b + 1)) → Buch.T (b + 1)) =>
    lfold Tr.zero Tr.succ Tr.lim q x) ?_).trans (lfold_cmap thr h x)
  funext μ rs
  exact eval_ifLtT _ _ _ _ _

theorem eval_dropT (a : Nat) {Γ : List Ty} (ρ : Env Γ) (h : Nat → Buch.T a) :
    eval (dropT a : Tm Γ _) ρ = Tr.cmap 0 h :=
  funext fun x => by
    show lfold Tr.zero Tr.succ Tr.lim (fun _ _ => Tr.zero) x = Tr.cmap 0 h x
    exact lfold_cmap0 h x

theorem eval_raiseT (b : Nat) {Γ : List Ty} (ρ : Env Γ) (h : Buch.P b → Nat) :
    eval (raiseT b : Tm Γ _) ρ = Tr.cmap 0 h :=
  funext fun x => by
    show lfold Tr.zero Tr.succ Tr.lim (fun _ _ => Tr.zero) x = Tr.cmap 0 h x
    exact lfold_cmap0 h x

theorem eval_add0T {Γ : List Ty} (ρ : Env Γ) (a b : Buch.T 0) :
    eval (add0T : Tm Γ _) ρ a b = Tr.add a b := lfold_add a b

theorem eval_supVia0T {Γ : List Ty} (ρ : Env Γ) (μ : Nat) :
    eval (supVia0T : Tm Γ _) ρ μ = Tr.sup μ (fun _ => Tr.zero) := rfl

theorem eval_mulNat0T {Γ : List Ty} (ρ : Env Γ) (a : Buch.T 0) :
    ∀ k, eval (mulNat0T : Tm Γ _) ρ a k = Tr.mulNat a k
  | 0 => rfl
  | k + 1 => by
      show eval (add0T : Tm _ _) _ (eval (mulNat0T : Tm Γ _) ρ a k) a = _
      rw [eval_add0T, eval_mulNat0T ρ a k]
      rfl

theorem eval_ifLtC {Γ : List Ty} {r : Ty} (ρ : Env Γ) (μ c : Nat) (a b : den r) :
    eval (ifLtC : Tm Γ (.arr .nat (.arr .nat (.arr r (.arr r r))))) ρ μ c a b =
      if μ < c then a else b :=
  eval_ifLtT (Γ := r :: r :: .nat :: .nat :: Γ) v3 v2 v1 v0 _

theorem eval_toB0T {Γ : List Ty} (ρ : Env Γ) : eval (toB0T : Tm Γ _) ρ = Tr.toB :=
  funext lfold_toB

theorem eval_tfbShell (θ : BTree) : eval tfbShell env0 θ = hardy θ (hardy θ 42) := by
  show eval (hardyT : Tm _ _) _ θ (eval (hardyT : Tm _ _) _ θ (eval (numT 42 : Tm _ .nat) _)) = _
  rw [eval_hardyT, eval_hardyT, eval_numT]

end Buchholz

end BusyLean.Indep.TT
