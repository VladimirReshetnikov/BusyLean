import BusyLean.SystemFLV.Types
import BusyLean.SystemFT2.Syntax

/-!
# Curry-style typing for the ladder with universe levels

As for `SystemFLT2`, with a level context `Λ` (the bounds of the level
variables), and two more rules: **level generalization** (`lgen`: a term typed
under a new level variable `b ≤ l` has type `∀b ≤ l. A`) and **level
instantiation** (`linst`: at any level `c` the bounds force to be `≤ l`).
Terms are those of System FT2, so levels, like types and kinds, are erased.
-/

namespace BusyLean.FLV

open BusyLean.FL (AtomOrder)
open BusyLean.FT2 (Tm)
open Ty

variable {α : Type} [DecidableEq α] [AtomOrder α]

abbrev Ctx (α : Type) := Nat → Ty α

def Ctx.cons (A : Ty α) (Γ : Ctx α) : Ctx α := tcons A Γ

def Ctx.lift (Γ : Ctx α) : Ctx α := fun n => tren Nat.succ (Γ n)

def Ctx.klift0 (Γ : Ctx α) : Ctx α := fun n => Ty.kren Nat.succ id (Γ n)

def Ctx.klift1 (Γ : Ctx α) : Ctx α := fun n => Ty.kren id Nat.succ (Γ n)

/-- Shift the level variables of a context, to enter a level binder. -/
def Ctx.llift (Γ : Ctx α) : Ctx α := fun n => (Γ n).lsh

inductive Typed (o : Bool) : List (Lvl α) → KCtx α → Ctx α → Tm → Ty α → Prop where
  | var {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} (n : Nat) : Typed o Λ Δ Γ (Tm.var n) (Γ n)
  | lam {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {A B : Ty α} {t : Tm} :
      Typed o Λ Δ (Ctx.cons A Γ) t B → Typed o Λ Δ Γ (Tm.lam t) (arr A B)
  | app {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {A B : Ty α} {t u : Tm} :
      Typed o Λ Δ Γ t (arr A B) → Typed o Λ Δ Γ u A → Typed o Λ Δ Γ (Tm.app t u) B
  | gen {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {k : Kind α} {A : Ty α} {t : Tm} :
      Typed o Λ (kcons k Δ) (Ctx.lift Γ) t A → Typed o Λ Δ Γ t (all k A)
  | inst {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {k : Kind α} {A : Ty α} {t : Tm} (B : Ty α) :
      Typed o Λ Δ Γ t (all k A) → Kinded Λ (kcons k Δ) A .star → Kinded Λ Δ B k →
      Typed o Λ Δ Γ t (Ty.inst A B)
  | conv {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {A B : Ty α} {t : Tm} :
      Typed o Λ Δ Γ t A → Kinded Λ Δ A .star → Kinded Λ Δ B .star → TJoin A B →
      Typed o Λ Δ Γ t B
  | kgen0 {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {A : Ty α} {t : Tm} :
      Typed o Λ Δ.klift0 (Ctx.klift0 Γ) t A → Typed o Λ Δ Γ t (kall0 A)
  | kinst0 {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {A : Ty α} {t : Tm} (K : Kind α) :
      Typed o Λ Δ Γ t (kall0 A) → K.DynFree → Typed o Λ Δ Γ t (Ty.kinst0 A K)
  | kgen1 {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {A : Ty α} {t : Tm} :
      Typed o Λ Δ.klift1 (Ctx.klift1 Γ) t A → Typed o Λ Δ Γ t (kall1 A)
  | kinst1 {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {A : Ty α} {t : Tm} (K : Kind α) :
      Typed o Λ Δ Γ t (kall1 A) → Typed o Λ Δ Γ t (Ty.kinst1 A K)
  | lgen {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {l : Lvl α} {A : Ty α} {t : Tm} :
      Typed o (l :: Λ) Δ.llift (Ctx.llift Γ) t A → Typed o Λ Δ Γ t (lall l A)
  | linst {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {l : Lvl α} {A : Ty α} {t : Tm} (c : Lvl α) :
      Typed o Λ Δ Γ t (lall l A) → lle Λ c l = true → Typed o Λ Δ Γ t (A.linst c)
  | orc {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} :
      o = true → Typed o Λ Δ Γ Tm.orc (arr Ty.nat Ty.nat)

theorem typed_iterApp (o : Bool) (Λ : List (Lvl α)) (Δ : KCtx α) (Γ : Ctx α) (X : Ty α) :
    ∀ n, Typed o Λ Δ (Ctx.cons X (Ctx.cons (arr X X) Γ)) (Tm.iterApp n) X
  | 0 => Typed.var 0
  | n + 1 => Typed.app (Typed.var 1) (typed_iterApp o Λ Δ Γ X n)

theorem typed_num (o : Bool) (Λ : List (Lvl α)) (Δ : KCtx α) (Γ : Ctx α) (n : Nat) :
    Typed o Λ Δ Γ (Tm.num n) Ty.nat :=
  Typed.gen (Typed.lam (Typed.lam (typed_iterApp o _ _ _ (tvar 0) n)))

end BusyLean.FLV
