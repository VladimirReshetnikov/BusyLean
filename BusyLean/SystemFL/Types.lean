import BusyLean.SystemFw.Types

/-!
# The ladder of dynamic kinds: syntax, kinding, type-level reduction

Contender 13's language, made **parametric in a type `α` of base atoms**.
Kinds are `★ | κ → κ | atom a | kvar | dvar | dyn`. Atoms are dyn-free, so
they may be packed into `dyn`.

Instantiating `α` with the atoms of a lower level, where each atom denotes
that level's `dyn`, yields a ladder of predicative universes
`dyn₀ ⊂ dyn₁ ⊂ ⋯`, assembled in `BusyLean/SystemFL/Ladder.lean`. The syntax
and its metatheory here are uniform in `α`.
-/

namespace BusyLean.FL

/-- The order on atoms: `lt b a` means atom `b` may be packed into atom `a`. -/
class AtomOrder (α : Type) where
  lt : α → α → Bool

variable {α : Type}

open BusyLean.F.Tm (upRen)

inductive Kind (α : Type) where
  | star : (Kind α)
  | arr : (Kind α) → (Kind α) → (Kind α)
  | kvar : Nat → (Kind α)
  | dvar : Nat → (Kind α)
  | dyn : (Kind α)
  | atom : α → (Kind α)
  deriving DecidableEq

namespace Kind

/-- Rename level-0 and level-1 kind variables. -/
def ren (ξ₀ ξ₁ : Nat → Nat) : (Kind α) → (Kind α)
  | star => star
  | arr a b => arr (ren ξ₀ ξ₁ a) (ren ξ₀ ξ₁ b)
  | kvar n => kvar (ξ₀ n)
  | dvar n => dvar (ξ₁ n)
  | dyn => dyn
  | atom a => atom a

/-- Substitute for level-0 and level-1 kind variables. -/
def subst (σ₀ σ₁ : Nat → (Kind α)) : (Kind α) → (Kind α)
  | star => star
  | arr a b => arr (subst σ₀ σ₁ a) (subst σ₀ σ₁ b)
  | kvar n => σ₀ n
  | dvar n => σ₁ n
  | dyn => dyn
  | atom a => atom a

def kcons (K : (Kind α)) (σ : Nat → (Kind α)) : Nat → (Kind α)
  | 0 => K
  | n + 1 => σ n

/-- Dyn-free kinds: no `dyn` and no level-1 variable. -/
def DynFree : (Kind α) → Prop
  | star => True
  | arr a b => DynFree a ∧ DynFree b
  | kvar _ => True
  | dvar _ => False
  | dyn => False
  | atom _ => True

def dynFree : (Kind α) → Bool
  | star => true
  | arr a b => dynFree a && dynFree b
  | kvar _ => true
  | dvar _ => false
  | dyn => false
  | atom _ => true

theorem dynFree_iff : ∀ K : (Kind α), dynFree K = true ↔ DynFree K
  | star => by simp [dynFree, DynFree]
  | arr a b => by simp [dynFree, DynFree, dynFree_iff a, dynFree_iff b]
  | kvar _ => by simp [dynFree, DynFree]
  | dvar _ => by simp [dynFree, DynFree]
  | dyn => by simp [dynFree, DynFree]
  | atom _ => by simp [dynFree, DynFree]

theorem ren_ren : ∀ (K : (Kind α)) (ξ₀ ξ₁ ζ₀ ζ₁ : Nat → Nat),
    ren ξ₀ ξ₁ (ren ζ₀ ζ₁ K) = ren (ξ₀ ∘ ζ₀) (ξ₁ ∘ ζ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, ren_ren a, ren_ren b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl
  | atom _, _, _, _, _ => rfl

theorem subst_ren : ∀ (K : (Kind α)) (σ₀ σ₁ : Nat → (Kind α)) (ξ₀ ξ₁ : Nat → Nat),
    subst σ₀ σ₁ (ren ξ₀ ξ₁ K) = subst (σ₀ ∘ ξ₀) (σ₁ ∘ ξ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, subst, subst_ren a, subst_ren b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl
  | atom _, _, _, _, _ => rfl

theorem ren_subst : ∀ (K : (Kind α)) (σ₀ σ₁ : Nat → (Kind α)) (ξ₀ ξ₁ : Nat → Nat),
    ren ξ₀ ξ₁ (subst σ₀ σ₁ K) = subst (ren ξ₀ ξ₁ ∘ σ₀) (ren ξ₀ ξ₁ ∘ σ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, subst, ren_subst a, ren_subst b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl
  | atom _, _, _, _, _ => rfl

theorem subst_subst : ∀ (K : (Kind α)) (σ₀ σ₁ τ₀ τ₁ : Nat → (Kind α)),
    subst σ₀ σ₁ (subst τ₀ τ₁ K) = subst (subst σ₀ σ₁ ∘ τ₀) (subst σ₀ σ₁ ∘ τ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [subst, subst_subst a, subst_subst b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl
  | atom _, _, _, _, _ => rfl

theorem subst_var : ∀ K : (Kind α), subst kvar dvar K = K
  | star => rfl
  | arr a b => by simp only [subst, subst_var a, subst_var b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl
  | atom _ => rfl

theorem DynFree.ren {K : (Kind α)} (h : DynFree K) (ξ₀ ξ₁ : Nat → Nat) : DynFree (ren ξ₀ ξ₁ K) := by
  induction K with
  | star => trivial
  | arr a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | kvar _ => trivial
  | dvar _ => exact h.elim
  | dyn => exact h.elim
  | atom _ => trivial

theorem DynFree.subst {K : (Kind α)} (h : DynFree K) {σ₀ σ₁ : Nat → (Kind α)}
    (hσ : ∀ n, DynFree (σ₀ n)) : DynFree (subst σ₀ σ₁ K) := by
  induction K with
  | star => trivial
  | arr a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | kvar n => exact hσ n
  | dvar _ => exact h.elim
  | dyn => exact h.elim
  | atom _ => trivial

/-- `K` is closed (no kind variable, no `dyn`) and all its atoms lie below `a`:
the kinds whose operators can be packed into the atom `a`. -/
def Fits [AtomOrder α] (a : α) : Kind α → Prop
  | star => True
  | arr x y => Fits a x ∧ Fits a y
  | atom b => AtomOrder.lt b a = true
  | kvar _ => False
  | dvar _ => False
  | dyn => False

def fits [AtomOrder α] (a : α) : Kind α → Bool
  | star => true
  | arr x y => fits a x && fits a y
  | atom b => AtomOrder.lt b a
  | kvar _ => false
  | dvar _ => false
  | dyn => false

theorem fits_iff [AtomOrder α] (a : α) : ∀ K : Kind α, fits a K = true ↔ Fits a K
  | star => by simp [fits, Fits]
  | arr x y => by simp [fits, Fits, fits_iff a x, fits_iff a y]
  | atom _ => by simp [fits, Fits]
  | kvar _ => by simp [fits, Fits]
  | dvar _ => by simp [fits, Fits]
  | dyn => by simp [fits, Fits]

/-- Fitting kinds are closed, hence fixed by renaming and substitution. -/
theorem Fits.ren_eq [AtomOrder α] {a : α} {K : Kind α} (h : Fits a K) (ξ₀ ξ₁ : Nat → Nat) :
    ren ξ₀ ξ₁ K = K := by
  induction K with
  | star => rfl
  | arr x y ihx ihy => simp only [ren, ihx h.1, ihy h.2]
  | atom _ => rfl
  | kvar _ => exact h.elim
  | dvar _ => exact h.elim
  | dyn => exact h.elim

theorem Fits.subst_eq [AtomOrder α] {a : α} {K : Kind α} (h : Fits a K) (σ₀ σ₁ : Nat → Kind α) :
    subst σ₀ σ₁ K = K := by
  induction K with
  | star => rfl
  | arr x y ihx ihy => simp only [subst, ihx h.1, ihy h.2]
  | atom _ => rfl
  | kvar _ => exact h.elim
  | dvar _ => exact h.elim
  | dyn => exact h.elim

/-- Shifts for entering a level-0 / level-1 kind binder. -/
def sh₀ (K : (Kind α)) : (Kind α) := ren Nat.succ id K
def sh₁ (K : (Kind α)) : (Kind α) := ren id Nat.succ K

end Kind

variable [AtomOrder α]

inductive Ty (α : Type) where
  | tvar : Nat → (Ty α)
  | arr : (Ty α) → (Ty α) → (Ty α)
  | all : (Kind α) → (Ty α) → (Ty α)
  | lam : (Kind α) → (Ty α) → (Ty α)
  | app : (Kind α) → (Ty α) → (Ty α) → (Ty α)
  | kall0 : (Ty α) → (Ty α)
  | kall1 : (Ty α) → (Ty α)
  | pack : (Kind α) → (Ty α) → (Ty α)
  | unpack : (Kind α) → (Ty α) → (Ty α)
  | apack : α → (Kind α) → (Ty α) → (Ty α)
  | aunpack : α → (Kind α) → (Ty α) → (Ty α)
  deriving DecidableEq

namespace Ty

def tren (ξ : Nat → Nat) : (Ty α) → (Ty α)
  | tvar n => tvar (ξ n)
  | arr A B => arr (tren ξ A) (tren ξ B)
  | all k A => all k (tren (upRen ξ) A)
  | lam k A => lam k (tren (upRen ξ) A)
  | app k A B => app k (tren ξ A) (tren ξ B)
  | kall0 A => kall0 (tren ξ A)
  | kall1 A => kall1 (tren ξ A)
  | pack k A => pack k (tren ξ A)
  | unpack k A => unpack k (tren ξ A)
  | apack a k A => apack a k (tren ξ A)
  | aunpack a k A => aunpack a k (tren ξ A)

/-- Rename kind variables of both levels. -/
def kren (ξ₀ ξ₁ : Nat → Nat) : (Ty α) → (Ty α)
  | tvar n => tvar n
  | arr A B => arr (kren ξ₀ ξ₁ A) (kren ξ₀ ξ₁ B)
  | all k A => all (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | lam k A => lam (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | app k A B => app (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A) (kren ξ₀ ξ₁ B)
  | kall0 A => kall0 (kren (upRen ξ₀) ξ₁ A)
  | kall1 A => kall1 (kren ξ₀ (upRen ξ₁) A)
  | pack k A => pack (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | unpack k A => unpack (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | apack a k A => apack a (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | aunpack a k A => aunpack a (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)

/-- Lift kind substitutions under a level-0 binder. -/
def kup₀ (σ₀ σ₁ : Nat → (Kind α)) : (Nat → (Kind α)) × (Nat → (Kind α)) :=
  (Kind.kcons (.kvar 0) (fun n => (σ₀ n).sh₀), fun n => (σ₁ n).sh₀)

/-- Lift kind substitutions under a level-1 binder. -/
def kup₁ (σ₀ σ₁ : Nat → (Kind α)) : (Nat → (Kind α)) × (Nat → (Kind α)) :=
  (fun n => (σ₀ n).sh₁, Kind.kcons (.dvar 0) (fun n => (σ₁ n).sh₁))

def ksubst (σ₀ σ₁ : Nat → (Kind α)) : (Ty α) → (Ty α)
  | tvar n => tvar n
  | arr A B => arr (ksubst σ₀ σ₁ A) (ksubst σ₀ σ₁ B)
  | all k A => all (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | lam k A => lam (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | app k A B => app (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A) (ksubst σ₀ σ₁ B)
  | kall0 A => kall0 (ksubst (kup₀ σ₀ σ₁).1 (kup₀ σ₀ σ₁).2 A)
  | kall1 A => kall1 (ksubst (kup₁ σ₀ σ₁).1 (kup₁ σ₀ σ₁).2 A)
  | pack k A => pack (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | unpack k A => unpack (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | apack a k A => apack a (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | aunpack a k A => aunpack a (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)

def tcons (B : (Ty α)) (σ : Nat → (Ty α)) : Nat → (Ty α)
  | 0 => B
  | n + 1 => σ n

def tup (σ : Nat → (Ty α)) : Nat → (Ty α) := tcons (tvar 0) (fun n => tren Nat.succ (σ n))

def tsubst (σ : Nat → (Ty α)) : (Ty α) → (Ty α)
  | tvar n => σ n
  | arr A B => arr (tsubst σ A) (tsubst σ B)
  | all k A => all k (tsubst (tup σ) A)
  | lam k A => lam k (tsubst (tup σ) A)
  | app k A B => app k (tsubst σ A) (tsubst σ B)
  | kall0 A => kall0 (tsubst (fun n => kren Nat.succ id (σ n)) A)
  | kall1 A => kall1 (tsubst (fun n => kren id Nat.succ (σ n)) A)
  | pack k A => pack k (tsubst σ A)
  | unpack k A => unpack k (tsubst σ A)
  | apack a k A => apack a k (tsubst σ A)
  | aunpack a k A => aunpack a k (tsubst σ A)

def inst (A B : (Ty α)) : (Ty α) := tsubst (tcons B tvar) A

def kinst0 (A : (Ty α)) (K : (Kind α)) : (Ty α) := ksubst (Kind.kcons K .kvar) .dvar A
def kinst1 (A : (Ty α)) (K : (Kind α)) : (Ty α) := ksubst .kvar (Kind.kcons K .dvar) A

def nat : (Ty α) := all .star (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0)))

end Ty

open Ty

/-! ## Kinding -/

abbrev KCtx (α : Type) := Nat → (Kind α)

def kcons (k : (Kind α)) (Δ : (KCtx α)) : (KCtx α)
  | 0 => k
  | n + 1 => Δ n

def KCtx.klift0 (Δ : (KCtx α)) : (KCtx α) := fun n => (Δ n).sh₀
def KCtx.klift1 (Δ : (KCtx α)) : (KCtx α) := fun n => (Δ n).sh₁

inductive Kinded : (KCtx α) → (Ty α) → (Kind α) → Prop where
  | tvar {Δ : (KCtx α)} (n : Nat) : Kinded Δ (tvar n) (Δ n)
  | arr {Δ : (KCtx α)} {A B : (Ty α)} :
      Kinded Δ A .star → Kinded Δ B .star → Kinded Δ (arr A B) .star
  | all {Δ : (KCtx α)} {k : (Kind α)} {A : (Ty α)} :
      Kinded (kcons k Δ) A .star → Kinded Δ (all k A) .star
  | lam {Δ : (KCtx α)} {k₁ k₂ : (Kind α)} {A : (Ty α)} :
      Kinded (kcons k₁ Δ) A k₂ → Kinded Δ (lam k₁ A) (.arr k₁ k₂)
  | app {Δ : (KCtx α)} {k₁ k₂ : (Kind α)} {A B : (Ty α)} :
      Kinded Δ A (.arr k₁ k₂) → Kinded Δ B k₁ → Kinded Δ (app k₁ A B) k₂
  | kall0 {Δ : (KCtx α)} {A : (Ty α)} : Kinded Δ.klift0 A .star → Kinded Δ (kall0 A) .star
  | kall1 {Δ : (KCtx α)} {A : (Ty α)} : Kinded Δ.klift1 A .star → Kinded Δ (kall1 A) .star
  | pack {Δ : (KCtx α)} {k : (Kind α)} {A : (Ty α)} :
      Kinded Δ A k → k.DynFree → Kinded Δ (pack k A) .dyn
  | unpack {Δ : (KCtx α)} {k : (Kind α)} {A : (Ty α)} :
      Kinded Δ A .dyn → k.DynFree → Kinded Δ (unpack k A) k
  | apack {Δ : (KCtx α)} {a : α} {k : (Kind α)} {A : (Ty α)} :
      Kinded Δ A k → k.Fits a → Kinded Δ (apack a k A) (.atom a)
  | aunpack {Δ : (KCtx α)} {a : α} {k : (Kind α)} {A : (Ty α)} :
      Kinded Δ A (.atom a) → k.Fits a → Kinded Δ (aunpack a k A) k

theorem Kinded.ren {Δ : (KCtx α)} {A : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) :
    ∀ {Δ' : (KCtx α)} {ξ : Nat → Nat}, (∀ n, Δ' (ξ n) = Δ n) → Kinded Δ' (tren ξ A) k := by
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

theorem Kinded.kren {Δ : (KCtx α)} {A : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) :
    ∀ (ξ₀ ξ₁ : Nat → Nat),
      Kinded (fun n => (Δ n).ren ξ₀ ξ₁) (Ty.kren ξ₀ ξ₁ A) (k.ren ξ₀ ξ₁) := by
  induction h with
  | tvar n => intro ξ₀ ξ₁; exact Kinded.tvar n
  | arr _ _ ih₁ ih₂ => intro ξ₀ ξ₁; exact Kinded.arr (ih₁ ξ₀ ξ₁) (ih₂ ξ₀ ξ₁)
  | @all Δ k A _ ih =>
      intro ξ₀ ξ₁
      refine Kinded.all ?_
      have e : (fun n => (kcons k Δ n).ren ξ₀ ξ₁) =
          kcons (k.ren ξ₀ ξ₁) (fun n => (Δ n).ren ξ₀ ξ₁) := by
        funext n; cases n <;> rfl
      have := ih ξ₀ ξ₁
      rw [e] at this
      exact this
  | @lam Δ k₁ k₂ A _ ih =>
      intro ξ₀ ξ₁
      refine Kinded.lam ?_
      have e : (fun n => (kcons k₁ Δ n).ren ξ₀ ξ₁) =
          kcons (k₁.ren ξ₀ ξ₁) (fun n => (Δ n).ren ξ₀ ξ₁) := by
        funext n; cases n <;> rfl
      have := ih ξ₀ ξ₁
      rw [e] at this
      exact this
  | app _ _ ih₁ ih₂ => intro ξ₀ ξ₁; exact Kinded.app (ih₁ ξ₀ ξ₁) (ih₂ ξ₀ ξ₁)
  | @kall0 Δ A _ ih =>
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
  | @kall1 Δ A _ ih =>
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
  | @apack Δ a k A _ hk ih =>
      intro ξ₀ ξ₁
      have e := hk.ren_eq ξ₀ ξ₁
      have h := ih ξ₀ ξ₁
      rw [e] at h
      show Kinded _ (Ty.apack a (k.ren ξ₀ ξ₁) _) _
      rw [e]
      exact Kinded.apack h hk
  | @aunpack Δ a k A _ hk ih =>
      intro ξ₀ ξ₁
      have e := hk.ren_eq ξ₀ ξ₁
      show Kinded _ (Ty.aunpack a (k.ren ξ₀ ξ₁) _) (k.ren ξ₀ ξ₁)
      rw [e]
      exact Kinded.aunpack (ih ξ₀ ξ₁) hk

theorem Kinded.ksubst {Δ : (KCtx α)} {A : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) :
    ∀ (σ₀ σ₁ : Nat → (Kind α)), (∀ n, (σ₀ n).DynFree) →
      Kinded (fun n => (Δ n).subst σ₀ σ₁) (Ty.ksubst σ₀ σ₁ A) (k.subst σ₀ σ₁) := by
  induction h with
  | tvar n => intro σ₀ σ₁ _; exact Kinded.tvar n
  | arr _ _ ih₁ ih₂ => intro σ₀ σ₁ hσ; exact Kinded.arr (ih₁ σ₀ σ₁ hσ) (ih₂ σ₀ σ₁ hσ)
  | @all Δ k A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.all ?_
      have e : (fun n => (kcons k Δ n).subst σ₀ σ₁) =
          kcons (k.subst σ₀ σ₁) (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n; cases n <;> rfl
      have := ih σ₀ σ₁ hσ
      rw [e] at this
      exact this
  | @lam Δ k₁ k₂ A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.lam ?_
      have e : (fun n => (kcons k₁ Δ n).subst σ₀ σ₁) =
          kcons (k₁.subst σ₀ σ₁) (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n; cases n <;> rfl
      have := ih σ₀ σ₁ hσ
      rw [e] at this
      exact this
  | app _ _ ih₁ ih₂ => intro σ₀ σ₁ hσ; exact Kinded.app (ih₁ σ₀ σ₁ hσ) (ih₂ σ₀ σ₁ hσ)
  | @kall0 Δ A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.kall0 ?_
      have hσ' : ∀ n, ((kup₀ σ₀ σ₁).1 n).DynFree := fun n => by
        cases n with
        | zero => trivial
        | succ n => exact (hσ n).ren _ _
      have := ih (kup₀ σ₀ σ₁).1 (kup₀ σ₀ σ₁).2 hσ'
      have e : (fun n => (Δ.klift0 n).subst (kup₀ σ₀ σ₁).1 (kup₀ σ₀ σ₁).2) =
          KCtx.klift0 (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n
        show ((Δ n).ren Nat.succ id).subst _ _ = ((Δ n).subst σ₀ σ₁).ren Nat.succ id
        rw [Kind.subst_ren, Kind.ren_subst]; rfl
      rw [e] at this
      exact this
  | @kall1 Δ A _ ih =>
      intro σ₀ σ₁ hσ
      refine Kinded.kall1 ?_
      have hσ' : ∀ n, ((kup₁ σ₀ σ₁).1 n).DynFree := fun n => (hσ n).ren _ _
      have := ih (kup₁ σ₀ σ₁).1 (kup₁ σ₀ σ₁).2 hσ'
      have e : (fun n => (Δ.klift1 n).subst (kup₁ σ₀ σ₁).1 (kup₁ σ₀ σ₁).2) =
          KCtx.klift1 (fun n => (Δ n).subst σ₀ σ₁) := by
        funext n
        show ((Δ n).ren id Nat.succ).subst _ _ = ((Δ n).subst σ₀ σ₁).ren id Nat.succ
        rw [Kind.subst_ren, Kind.ren_subst]; rfl
      rw [e] at this
      exact this
  | pack _ hk ih => intro σ₀ σ₁ hσ; exact Kinded.pack (ih σ₀ σ₁ hσ) (hk.subst hσ)
  | unpack _ hk ih => intro σ₀ σ₁ hσ; exact Kinded.unpack (ih σ₀ σ₁ hσ) (hk.subst hσ)
  | @apack Δ a k A _ hk ih =>
      intro σ₀ σ₁ hσ
      have e := hk.subst_eq σ₀ σ₁
      have h := ih σ₀ σ₁ hσ
      rw [e] at h
      show Kinded _ (Ty.apack a (k.subst σ₀ σ₁) _) _
      rw [e]
      exact Kinded.apack h hk
  | @aunpack Δ a k A _ hk ih =>
      intro σ₀ σ₁ hσ
      have e := hk.subst_eq σ₀ σ₁
      show Kinded _ (Ty.aunpack a (k.subst σ₀ σ₁) _) (k.subst σ₀ σ₁)
      rw [e]
      exact Kinded.aunpack (ih σ₀ σ₁ hσ) hk

theorem Kinded.subst {Δ : (KCtx α)} {A : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) :
    ∀ {Δ' : (KCtx α)} {σ : Nat → (Ty α)}, (∀ n, Kinded Δ' (σ n) (Δ n)) →
      Kinded Δ' (tsubst σ A) k := by
  induction h with
  | tvar n => intro Δ' σ hσ; exact hσ n
  | arr _ _ ih₁ ih₂ => intro Δ' σ hσ; exact Kinded.arr (ih₁ hσ) (ih₂ hσ)
  | @all Δ k A _ ih =>
      intro Δ' σ hσ
      refine Kinded.all (ih fun n => ?_)
      cases n with
      | zero => exact Kinded.tvar 0
      | succ n => exact (hσ n).ren fun _ => rfl
  | @lam Δ k₁ k₂ A _ ih =>
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

theorem Kinded.inst {Δ : (KCtx α)} {k k' : (Kind α)} {A B : (Ty α)}
    (hA : Kinded (kcons k Δ) A k') (hB : Kinded Δ B k) : Kinded Δ (Ty.inst A B) k' :=
  hA.subst fun n => by
    cases n with
    | zero => exact hB
    | succ n => exact Kinded.tvar n

theorem Kinded.kinst0 {Δ : (KCtx α)} {A : (Ty α)} (hA : Kinded Δ.klift0 A .star) {K : (Kind α)}
    (hK : K.DynFree) : Kinded Δ (Ty.kinst0 A K) .star := by
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

theorem Kinded.kinst1 {Δ : (KCtx α)} {A : (Ty α)} (hA : Kinded Δ.klift1 A .star) (K : (Kind α)) :
    Kinded Δ (Ty.kinst1 A K) .star := by
  have h := hA.ksubst .kvar (Kind.kcons K .dvar) fun _ => trivial
  have e : (fun n => (Δ.klift1 n).subst .kvar (Kind.kcons K .dvar)) = Δ := by
    funext n
    show ((Δ n).ren id Nat.succ).subst _ _ = Δ n
    rw [Kind.subst_ren]
    exact Kind.subst_var (Δ n)
  rw [e] at h
  exact h

theorem Kinded.nat (Δ : (KCtx α)) : Kinded Δ Ty.nat .star :=
  Kinded.all (Kinded.arr (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0))
    (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0)))

/-! ## Type-level reduction -/

inductive TStep : (Ty α) → (Ty α) → Prop where
  | beta (k k' : (Kind α)) (A B : (Ty α)) : TStep (app k (lam k' A) B) (Ty.inst A B)
  | unpackPack (k : (Kind α)) (A : (Ty α)) : k.DynFree → TStep (unpack k (pack k A)) A
  | aunpackApack (a : α) (k : (Kind α)) (A : (Ty α)) :
      k.Fits a → TStep (aunpack a k (apack a k A)) A
  | arrL {A A' : (Ty α)} (B : (Ty α)) : TStep A A' → TStep (arr A B) (arr A' B)
  | arrR (A : (Ty α)) {B B' : (Ty α)} : TStep B B' → TStep (arr A B) (arr A B')
  | all (k : (Kind α)) {A A' : (Ty α)} : TStep A A' → TStep (all k A) (all k A')
  | lam (k : (Kind α)) {A A' : (Ty α)} : TStep A A' → TStep (lam k A) (lam k A')
  | appL (k : (Kind α)) {A A' : (Ty α)} (B : (Ty α)) : TStep A A' → TStep (app k A B) (app k A' B)
  | appR (k : (Kind α)) (A : (Ty α)) {B B' : (Ty α)} : TStep B B' → TStep (app k A B) (app k A B')
  | kall0 {A A' : (Ty α)} : TStep A A' → TStep (kall0 A) (kall0 A')
  | kall1 {A A' : (Ty α)} : TStep A A' → TStep (kall1 A) (kall1 A')
  | pack (k : (Kind α)) {A A' : (Ty α)} : TStep A A' → TStep (pack k A) (pack k A')
  | unpack (k : (Kind α)) {A A' : (Ty α)} : TStep A A' → TStep (unpack k A) (unpack k A')
  | apack (a : α) (k : (Kind α)) {A A' : (Ty α)} : TStep A A' → TStep (apack a k A) (apack a k A')
  | aunpack (a : α) (k : (Kind α)) {A A' : (Ty α)} :
      TStep A A' → TStep (aunpack a k A) (aunpack a k A')

inductive TSteps : (Ty α) → (Ty α) → Prop where
  | refl (A : (Ty α)) : TSteps A A
  | step {A B C : (Ty α)} : TStep A B → TSteps B C → TSteps A C

def TJoin (A B : (Ty α)) : Prop := ∃ C, TSteps A C ∧ TSteps B C

theorem TSteps.join_left {A B : (Ty α)} (s : TSteps A B) : TJoin A B := ⟨B, s, TSteps.refl B⟩

theorem TJoin.symm {A B : (Ty α)} (j : TJoin A B) : TJoin B A := by
  obtain ⟨C, h₁, h₂⟩ := j
  exact ⟨C, h₂, h₁⟩

theorem Kinded.step {Δ : (KCtx α)} {A : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) {B : (Ty α)}
    (s : TStep A B) : Kinded Δ B k := by
  induction s generalizing Δ k with
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
  | aunpackApack a k A _ =>
      cases h with
      | aunpack hX _ =>
          cases hX with
          | apack hA _ => exact hA
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

theorem Kinded.steps {Δ : (KCtx α)} {A B : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) (s : TSteps A B) :
    Kinded Δ B k := by
  induction s with
  | refl => exact h
  | step s _ ih => exact ih (h.step s)

/-! ## A sound, fuel-bounded type normalizer -/

variable [DecidableEq α]

def tappCong (k : (Kind α)) (A B : (Ty α)) (sA sB : Option (Ty α)) : Option (Ty α) :=
  match sA with
  | some A' => some (app k A' B)
  | none => sB.map (app k A)

def tappStep (k : (Kind α)) (A B : (Ty α)) (sA sB : Option (Ty α)) : Option (Ty α) :=
  match A with
  | lam _ A₀ => some (Ty.inst A₀ B)
  | _ => tappCong k A B sA sB

/-- The atom-level unpack-of-pack redex, when atoms and kinds agree and the
kind fits the atom. -/
def aunpackRedex (a : α) (k : (Kind α)) (A : (Ty α)) : Option (Ty α) :=
  match A with
  | apack a' k' A₀ => if a' = a ∧ k' = k ∧ k.fits a = true then some A₀ else none
  | _ => none

/-- The unpack-of-pack redex, when the kinds agree and are dyn-free. -/
def unpackRedex (k : (Kind α)) (A : (Ty α)) : Option (Ty α) :=
  match A with
  | pack k' A₀ => if k' = k ∧ k.dynFree = true then some A₀ else none
  | _ => none

def tstep : (Ty α) → Option (Ty α)
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
  | apack a k A => (tstep A).map (apack a k)
  | aunpack a k A =>
      match aunpackRedex a k A with
      | some B => some B
      | none => (tstep A).map (aunpack a k)

omit [DecidableEq α] in
theorem tappCong_sound {k : (Kind α)} {A B C : (Ty α)} {sA sB : Option (Ty α)}
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
theorem tappStep_sound {k : (Kind α)} {A B C : (Ty α)} {sA sB : Option (Ty α)}
    (hA : ∀ A', sA = some A' → TStep A A') (hB : ∀ B', sB = some B' → TStep B B')
    (h : tappStep k A B sA sB = some C) : TStep (app k A B) C := by
  cases A with
  | lam k' A₀ => cases h; exact TStep.beta _ _ _ _
  | tvar _ => exact tappCong_sound hA hB h
  | arr _ _ => exact tappCong_sound hA hB h
  | all _ _ => exact tappCong_sound hA hB h
  | app _ _ _ => exact tappCong_sound hA hB h
  | kall0 _ => exact tappCong_sound hA hB h
  | kall1 _ => exact tappCong_sound hA hB h
  | pack _ _ => exact tappCong_sound hA hB h
  | unpack _ _ => exact tappCong_sound hA hB h
  | apack _ _ _ => exact tappCong_sound hA hB h
  | aunpack _ _ _ => exact tappCong_sound hA hB h

theorem unpackRedex_sound {k : (Kind α)} {A B : (Ty α)} (h : unpackRedex k A = some B) :
    TStep (unpack k A) B := by
  unfold unpackRedex at h
  cases A with
  | pack k' A₀ =>
      change (if k' = k ∧ k.dynFree = true then some A₀ else none) = some B at h
      by_cases e : k' = k ∧ k.dynFree = true
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, hk⟩ := e
        exact TStep.unpackPack _ _ ((Kind.dynFree_iff _).1 hk)
      · rw [ite_eq_right e] at h; cases h
  | tvar _ => cases h
  | arr _ _ => cases h
  | all _ _ => cases h
  | lam _ _ => cases h
  | app _ _ _ => cases h
  | kall0 _ => cases h
  | kall1 _ => cases h
  | unpack _ _ => cases h
  | apack _ _ _ => cases h
  | aunpack _ _ _ => cases h

theorem aunpackRedex_sound {a : α} {k : (Kind α)} {A B : (Ty α)}
    (h : aunpackRedex a k A = some B) : TStep (aunpack a k A) B := by
  unfold aunpackRedex at h
  cases A with
  | apack a' k' A₀ =>
      change (if a' = a ∧ k' = k ∧ k.fits a = true then some A₀ else none) = some B at h
      by_cases e : a' = a ∧ k' = k ∧ k.fits a = true
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, rfl, hk⟩ := e
        exact TStep.aunpackApack _ _ _ ((Kind.fits_iff _ _).1 hk)
      · rw [ite_eq_right e] at h; cases h
  | tvar _ => cases h
  | arr _ _ => cases h
  | all _ _ => cases h
  | lam _ _ => cases h
  | app _ _ _ => cases h
  | kall0 _ => cases h
  | kall1 _ => cases h
  | pack _ _ => cases h
  | unpack _ _ => cases h
  | aunpack _ _ _ => cases h

theorem tstep_sound : ∀ {A B : (Ty α)}, tstep A = some B → TStep A B
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
  | apack a k A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.apack _ _ (tstep_sound hA)
  | aunpack a k A, C, h => by
      simp only [tstep] at h
      cases hr : aunpackRedex a k A with
      | some B => rw [hr] at h; cases h; exact aunpackRedex_sound hr
      | none =>
          rw [hr] at h
          cases hA : tstep A with
          | none => rw [hA] at h; cases h
          | some A' => rw [hA] at h; cases h; exact TStep.aunpack _ _ (tstep_sound hA)

def tnf : Nat → (Ty α) → (Ty α)
  | 0, A => A
  | fuel + 1, A =>
      match tstep A with
      | some B => tnf fuel B
      | none => A

theorem tnf_steps : ∀ (fuel : Nat) (A : (Ty α)), TSteps A (tnf fuel A)
  | 0, A => TSteps.refl A
  | fuel + 1, A => by
      simp only [tnf]
      cases h : tstep A with
      | none => exact TSteps.refl A
      | some B => exact TSteps.step (tstep_sound h) (tnf_steps fuel B)

theorem tjoin_of_tnf {fuel : Nat} {A B : (Ty α)} (h : tnf fuel A = tnf fuel B) : TJoin A B :=
  ⟨tnf fuel A, tnf_steps fuel A, h ▸ tnf_steps fuel B⟩

/-! ## (Kind α) inference -/

open BusyLean.Fw (nth?)

def kctxOf (Δ : List (Kind α)) : (KCtx α) := fun n => (nth? Δ n).getD .star

omit [DecidableEq α] [AtomOrder α] in
theorem kctxOf_cons (k : (Kind α)) (Δ : List (Kind α)) : kctxOf (k :: Δ) = kcons k (kctxOf Δ) := by
  funext n; cases n <;> rfl

theorem nth?_map {α β : Type} (g : α → β) : ∀ (l : List α) (n : Nat),
    nth? (l.map g) n = (nth? l n).map g
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => nth?_map g l n

omit [DecidableEq α] [AtomOrder α] in
theorem kctxOf_klift0 (Δ : List (Kind α)) : kctxOf (Δ.map Kind.sh₀) = (kctxOf Δ).klift0 := by
  funext n
  show (nth? (Δ.map Kind.sh₀) n).getD .star = ((nth? Δ n).getD .star).sh₀
  rw [nth?_map]
  cases nth? Δ n <;> rfl

omit [DecidableEq α] [AtomOrder α] in
theorem kctxOf_klift1 (Δ : List (Kind α)) : kctxOf (Δ.map Kind.sh₁) = (kctxOf Δ).klift1 := by
  funext n
  show (nth? (Δ.map Kind.sh₁) n).getD .star = ((nth? Δ n).getD .star).sh₁
  rw [nth?_map]
  cases nth? Δ n <;> rfl

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

def apackK (a : α) (k : Kind α) : Option (Kind α) → Option (Kind α)
  | some k' => if k' = k ∧ k.fits a = true then some (.atom a) else none
  | none => none

def aunpackK (a : α) (k : Kind α) : Option (Kind α) → Option (Kind α)
  | some (.atom b) => if b = a ∧ k.fits a = true then some k else none
  | _ => none

def inferKind : List (Kind α) → (Ty α) → Option (Kind α)
  | Δ, tvar n => nth? Δ n
  | Δ, arr A B => arrK (inferKind Δ A) (inferKind Δ B)
  | Δ, all k A => starK (inferKind (k :: Δ) A)
  | Δ, lam k A => (inferKind (k :: Δ) A).map (Kind.arr k)
  | Δ, app k A B => appK k (inferKind Δ A) (inferKind Δ B)
  | Δ, kall0 A => starK (inferKind (Δ.map Kind.sh₀) A)
  | Δ, kall1 A => starK (inferKind (Δ.map Kind.sh₁) A)
  | Δ, pack k A => packK k (inferKind Δ A)
  | Δ, unpack k A => unpackK k (inferKind Δ A)
  | Δ, apack a k A => apackK a k (inferKind Δ A)
  | Δ, aunpack a k A => aunpackK a k (inferKind Δ A)

omit [AtomOrder α] [DecidableEq α] in
theorem starK_inv {o : Option (Kind α)} {k : Kind α} (h : starK o = some k) :
    o = some .star ∧ k = .star := by
  match o, h with
  | some .star, h => cases h; exact ⟨rfl, rfl⟩

omit [AtomOrder α] [DecidableEq α] in
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

theorem apackK_inv {a : α} {k r : Kind α} {x : Option (Kind α)} (h : apackK a k x = some r) :
    x = some k ∧ k.Fits a ∧ r = .atom a := by
  match x, h with
  | some k', h =>
      change (if k' = k ∧ k.fits a = true then some (Kind.atom a) else none) = some r at h
      by_cases e : k' = k ∧ k.fits a = true
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, hk⟩ := e
        exact ⟨rfl, (Kind.fits_iff _ _).1 hk, rfl⟩
      · rw [ite_eq_right e] at h; cases h

theorem aunpackK_inv {a : α} {k r : Kind α} {x : Option (Kind α)} (h : aunpackK a k x = some r) :
    x = some (.atom a) ∧ k.Fits a ∧ r = k := by
  match x, h with
  | some (.atom b), h =>
      change (if b = a ∧ k.fits a = true then some k else none) = some r at h
      by_cases e : b = a ∧ k.fits a = true
      · rw [ite_eq_left e] at h
        cases h
        obtain ⟨rfl, hk⟩ := e
        exact ⟨rfl, (Kind.fits_iff _ _).1 hk, rfl⟩
      · rw [ite_eq_right e] at h; cases h

theorem inferKind_sound : ∀ (A : (Ty α)) {Δ : List (Kind α)} {k : (Kind α)},
    inferKind Δ A = some k → Kinded (kctxOf Δ) A k
  | tvar n, Δ, k, h => by
      have e : kctxOf Δ n = k := by
        show (nth? Δ n).getD .star = k
        rw [show nth? Δ n = some k from h]; rfl
      rw [← e]; exact Kinded.tvar n
  | arr A B, Δ, k, h => by
      obtain ⟨hA, hB, rfl⟩ := arrK_inv (x := inferKind Δ A) (y := inferKind Δ B) h
      exact Kinded.arr (inferKind_sound A hA) (inferKind_sound B hB)
  | all k' A, Δ, k, h => by
      obtain ⟨hA, rfl⟩ := starK_inv (o := inferKind (k' :: Δ) A) h
      have ih := inferKind_sound A hA
      rw [kctxOf_cons] at ih
      exact Kinded.all ih
  | lam k' A, Δ, k, h => by
      change (inferKind (k' :: Δ) A).map (Kind.arr k') = some k at h
      cases hA : inferKind (k' :: Δ) A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          cases h
          have ih := inferKind_sound A hA
          rw [kctxOf_cons] at ih
          exact Kinded.lam ih
  | app k' A B, Δ, k, h => by
      obtain ⟨hA, hB⟩ := appK_inv (x := inferKind Δ A) (y := inferKind Δ B) h
      exact Kinded.app (inferKind_sound A hA) (inferKind_sound B hB)
  | kall0 A, Δ, k, h => by
      obtain ⟨hA, rfl⟩ := starK_inv (o := inferKind (Δ.map Kind.sh₀) A) h
      have ih := inferKind_sound A hA
      rw [kctxOf_klift0] at ih
      exact Kinded.kall0 ih
  | kall1 A, Δ, k, h => by
      obtain ⟨hA, rfl⟩ := starK_inv (o := inferKind (Δ.map Kind.sh₁) A) h
      have ih := inferKind_sound A hA
      rw [kctxOf_klift1] at ih
      exact Kinded.kall1 ih
  | pack k' A, Δ, k, h => by
      obtain ⟨hA, hk, rfl⟩ := packK_inv (x := inferKind Δ A) h
      exact Kinded.pack (inferKind_sound A hA) hk
  | unpack k' A, Δ, k, h => by
      obtain ⟨hA, hk, rfl⟩ := unpackK_inv (x := inferKind Δ A) h
      exact Kinded.unpack (inferKind_sound A hA) hk
  | apack a k' A, Δ, k, h => by
      obtain ⟨hA, hk, rfl⟩ := apackK_inv (x := inferKind Δ A) h
      exact Kinded.apack (inferKind_sound A hA) hk
  | aunpack a k' A, Δ, k, h => by
      obtain ⟨hA, hk, rfl⟩ := aunpackK_inv (x := inferKind Δ A) h
      exact Kinded.aunpack (inferKind_sound A hA) hk

end BusyLean.FL
