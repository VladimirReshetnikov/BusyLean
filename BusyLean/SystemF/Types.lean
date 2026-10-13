import BusyLean.SystemF.Syntax

/-!
# System F types and Curry-style typing

Types use de Bruijn indices for type variables. The typing judgment is
*Curry-style*: it types untyped (erased) terms. Its flag `o` says whether the
oracle rule is available. Numerals are typed without it, which lets the
normalization proof justify the oracle afterwards.
-/

namespace BusyLean.F

inductive Ty where
  | tvar : Nat → Ty
  | arr : Ty → Ty → Ty
  | all : Ty → Ty
  deriving DecidableEq

namespace Ty

def tren (ξ : Nat → Nat) : Ty → Ty
  | tvar n => tvar (ξ n)
  | arr A B => arr (tren ξ A) (tren ξ B)
  | all A => all (tren (Tm.upRen ξ) A)

def tcons (B : Ty) (σ : Nat → Ty) : Nat → Ty
  | 0 => B
  | n + 1 => σ n

def tup (σ : Nat → Ty) : Nat → Ty := tcons (tvar 0) (fun n => tren Nat.succ (σ n))

def tsubst (σ : Nat → Ty) : Ty → Ty
  | tvar n => σ n
  | arr A B => arr (tsubst σ A) (tsubst σ B)
  | all A => all (tsubst (tup σ) A)

/-- Instantiate the outermost bound variable of `∀A` with `B`. -/
def inst (A B : Ty) : Ty := tsubst (tcons B tvar) A

/-- Church numerals: `∀X. (X → X) → X → X`. -/
def nat : Ty := all (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0)))

theorem tren_nat (ξ : Nat → Nat) : tren ξ nat = nat := rfl

end Ty

open Tm Ty

/-- Typing contexts are total maps from de Bruijn indices to types. -/
abbrev Ctx := Nat → Ty

def Ctx.cons (A : Ty) (Γ : Ctx) : Ctx := tcons A Γ

/-- Shift every type in a context, when entering a type abstraction. -/
def Ctx.lift (Γ : Ctx) : Ctx := fun n => tren Nat.succ (Γ n)

/-- Curry-style System F typing of untyped terms, with oracle rule iff `o`. -/
inductive Typed (o : Bool) : Ctx → Tm → Ty → Prop where
  | var {Γ : Ctx} (n : Nat) : Typed o Γ (Tm.var n) (Γ n)
  | lam {Γ : Ctx} {A B : Ty} {t : Tm} :
      Typed o (Ctx.cons A Γ) t B → Typed o Γ (Tm.lam t) (arr A B)
  | app {Γ : Ctx} {A B : Ty} {t u : Tm} :
      Typed o Γ t (arr A B) → Typed o Γ u A → Typed o Γ (Tm.app t u) B
  | gen {Γ : Ctx} {A : Ty} {t : Tm} :
      Typed o (Ctx.lift Γ) t A → Typed o Γ t (all A)
  | inst {Γ : Ctx} {A : Ty} {t : Tm} (B : Ty) :
      Typed o Γ t (all A) → Typed o Γ t (Ty.inst A B)
  | orc {Γ : Ctx} : o = true → Typed o Γ Tm.orc (arr Ty.nat Ty.nat)

/-- The numeral body `fⁿ x` has type `X` when `f : X → X` and `x : X`. -/
theorem typed_iterApp (o : Bool) (Γ : Ctx) (X : Ty) :
    ∀ n, Typed o (Ctx.cons X (Ctx.cons (arr X X) Γ)) (iterApp n) X
  | 0 => Typed.var 0
  | n + 1 => Typed.app (Typed.var 1) (typed_iterApp o Γ X n)

/-- Every Church numeral has type `nat`, without the oracle rule. -/
theorem typed_num (o : Bool) (Γ : Ctx) (n : Nat) : Typed o Γ (num n) Ty.nat :=
  Typed.gen (Typed.lam (Typed.lam (typed_iterApp o _ (tvar 0) n)))

end BusyLean.F
