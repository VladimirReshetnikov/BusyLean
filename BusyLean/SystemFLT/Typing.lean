import BusyLean.SystemFL.Types
import BusyLean.SystemFT.Syntax

/-!
# Curry-style typing for the ladder language (parametric in atoms)

As for kind-polymorphic Fω, with kind generalization and instantiation at both
levels. Instantiating a level-0 kind variable requires a dyn-free kind.
-/

namespace BusyLean.FLT

open BusyLean.FL

variable {α : Type} [AtomOrder α]

open BusyLean.FT (Tm)
open Ty

abbrev Ctx (α : Type) := Nat → (Ty α)

def Ctx.cons (A : (Ty α)) (Γ : (Ctx α)) : (Ctx α) := tcons A Γ

def Ctx.lift (Γ : (Ctx α)) : (Ctx α) := fun n => tren Nat.succ (Γ n)

def Ctx.klift0 (Γ : (Ctx α)) : (Ctx α) := fun n => Ty.kren Nat.succ id (Γ n)

def Ctx.klift1 (Γ : (Ctx α)) : (Ctx α) := fun n => Ty.kren id Nat.succ (Γ n)

inductive Typed (o : Bool) : (KCtx α) → (Ctx α) → Tm → (Ty α) → Prop where
  | var {Δ : (KCtx α)} {Γ : (Ctx α)} (n : Nat) : Typed o Δ Γ (Tm.var n) (Γ n)
  | lam {Δ : (KCtx α)} {Γ : (Ctx α)} {A B : (Ty α)} {t : Tm} :
      Typed o Δ (Ctx.cons A Γ) t B → Typed o Δ Γ (Tm.lam t) (arr A B)
  | app {Δ : (KCtx α)} {Γ : (Ctx α)} {A B : (Ty α)} {t u : Tm} :
      Typed o Δ Γ t (arr A B) → Typed o Δ Γ u A → Typed o Δ Γ (Tm.app t u) B
  | gen {Δ : (KCtx α)} {Γ : (Ctx α)} {k : (Kind α)} {A : (Ty α)} {t : Tm} :
      Typed o (kcons k Δ) (Ctx.lift Γ) t A → Typed o Δ Γ t (all k A)
  | inst {Δ : (KCtx α)} {Γ : (Ctx α)} {k : (Kind α)} {A : (Ty α)} {t : Tm} (B : (Ty α)) :
      Typed o Δ Γ t (all k A) → Kinded (kcons k Δ) A .star → Kinded Δ B k →
      Typed o Δ Γ t (Ty.inst A B)
  | conv {Δ : (KCtx α)} {Γ : (Ctx α)} {A B : (Ty α)} {t : Tm} :
      Typed o Δ Γ t A → Kinded Δ A .star → Kinded Δ B .star → TJoin A B →
      Typed o Δ Γ t B
  | kgen0 {Δ : (KCtx α)} {Γ : (Ctx α)} {A : (Ty α)} {t : Tm} :
      Typed o Δ.klift0 (Ctx.klift0 Γ) t A → Typed o Δ Γ t (kall0 A)
  | kinst0 {Δ : (KCtx α)} {Γ : (Ctx α)} {A : (Ty α)} {t : Tm} (K : (Kind α)) :
      Typed o Δ Γ t (kall0 A) → K.DynFree → Typed o Δ Γ t (Ty.kinst0 A K)
  | kgen1 {Δ : (KCtx α)} {Γ : (Ctx α)} {A : (Ty α)} {t : Tm} :
      Typed o Δ.klift1 (Ctx.klift1 Γ) t A → Typed o Δ Γ t (kall1 A)
  | kinst1 {Δ : (KCtx α)} {Γ : (Ctx α)} {A : (Ty α)} {t : Tm} (K : (Kind α)) :
      Typed o Δ Γ t (kall1 A) → Typed o Δ Γ t (Ty.kinst1 A K)
  | orc {Δ : (KCtx α)} {Γ : (Ctx α)} : o = true → Typed o Δ Γ Tm.orc (arr Ty.nat Ty.nat)

theorem typed_iterApp (o : Bool) (Δ : (KCtx α)) (Γ : (Ctx α)) (X : (Ty α)) :
    ∀ n, Typed o Δ (Ctx.cons X (Ctx.cons (arr X X) Γ)) (Tm.iterApp n) X
  | 0 => Typed.var 0
  | n + 1 => Typed.app (Typed.var 1) (typed_iterApp o Δ Γ X n)

theorem typed_num (o : Bool) (Δ : (KCtx α)) (Γ : (Ctx α)) (n : Nat) :
    Typed o Δ Γ (Tm.num n) Ty.nat :=
  Typed.gen (Typed.lam (Typed.lam (typed_iterApp o _ _ (tvar 0) n)))

end BusyLean.FLT
