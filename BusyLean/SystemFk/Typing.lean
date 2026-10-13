import BusyLean.SystemFk.Types

/-!
# Curry-style typing for kind-polymorphic System Fω

As for Fω, with two new rules: kind generalization (`kgen`) and kind
instantiation (`kinst`). Neither leaves a trace in the erased term.
-/

namespace BusyLean.Fk

open BusyLean.F (Tm)
open Ty

abbrev Ctx := Nat → Ty

def Ctx.cons (A : Ty) (Γ : Ctx) : Ctx := tcons A Γ

/-- Shift type variables, entering a type binder. -/
def Ctx.lift (Γ : Ctx) : Ctx := fun n => tren Nat.succ (Γ n)

/-- Shift kind variables, entering a kind binder. -/
def Ctx.klift (Γ : Ctx) : Ctx := fun n => Ty.kren Nat.succ (Γ n)

inductive Typed (o : Bool) : KCtx → Ctx → Tm → Ty → Prop where
  | var {Δ : KCtx} {Γ : Ctx} (n : Nat) : Typed o Δ Γ (Tm.var n) (Γ n)
  | lam {Δ : KCtx} {Γ : Ctx} {A B : Ty} {t : Tm} :
      Typed o Δ (Ctx.cons A Γ) t B → Typed o Δ Γ (Tm.lam t) (arr A B)
  | app {Δ : KCtx} {Γ : Ctx} {A B : Ty} {t u : Tm} :
      Typed o Δ Γ t (arr A B) → Typed o Δ Γ u A → Typed o Δ Γ (Tm.app t u) B
  | gen {Δ : KCtx} {Γ : Ctx} {k : Kind} {A : Ty} {t : Tm} :
      Typed o (kcons k Δ) (Ctx.lift Γ) t A → Typed o Δ Γ t (all k A)
  | inst {Δ : KCtx} {Γ : Ctx} {k : Kind} {A : Ty} {t : Tm} (B : Ty) :
      Typed o Δ Γ t (all k A) → Kinded (kcons k Δ) A .star → Kinded Δ B k →
      Typed o Δ Γ t (Ty.inst A B)
  | conv {Δ : KCtx} {Γ : Ctx} {A B : Ty} {t : Tm} :
      Typed o Δ Γ t A → Kinded Δ A .star → Kinded Δ B .star → TJoin A B →
      Typed o Δ Γ t B
  | kgen {Δ : KCtx} {Γ : Ctx} {A : Ty} {t : Tm} :
      Typed o Δ.klift (Ctx.klift Γ) t A → Typed o Δ Γ t (kall A)
  | kinst {Δ : KCtx} {Γ : Ctx} {A : Ty} {t : Tm} (K : Kind) :
      Typed o Δ Γ t (kall A) → Typed o Δ Γ t (Ty.kinst A K)
  | orc {Δ : KCtx} {Γ : Ctx} : o = true → Typed o Δ Γ Tm.orc (arr Ty.nat Ty.nat)

theorem typed_iterApp (o : Bool) (Δ : KCtx) (Γ : Ctx) (X : Ty) :
    ∀ n, Typed o Δ (Ctx.cons X (Ctx.cons (arr X X) Γ)) (Tm.iterApp n) X
  | 0 => Typed.var 0
  | n + 1 => Typed.app (Typed.var 1) (typed_iterApp o Δ Γ X n)

theorem typed_num (o : Bool) (Δ : KCtx) (Γ : Ctx) (n : Nat) :
    Typed o Δ Γ (Tm.num n) Ty.nat :=
  Typed.gen (Typed.lam (Typed.lam (typed_iterApp o _ _ (tvar 0) n)))

end BusyLean.Fk
