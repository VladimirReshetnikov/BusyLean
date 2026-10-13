import BusyLean.SystemFw.Types

/-!
# System Fω with a dynamic kind: syntax, kinding, type-level reduction

This extends kind-polymorphic Fω with a predicative universe of operators:

* a kind `dyn`, whose elements are operators of *any* dyn-free kind,
  packaged with their kind (semantically `Σ k, Sem k`);
* type-level `pack K A : dyn` (for `A : K`) and `unpack K X : K`
  (for `X : dyn`), with the conversion `unpack K (pack K A) ⟶ A`;
* two sorts of kind variables: **level 0** (`kvar`, bound by `kall0`,
  ranging over dyn-free kinds) and **level 1** (`dvar`, bound by `kall1`,
  ranging over all kinds, including `dyn` and kinds built from it).

`pack`/`unpack` are only allowed at *dyn-free* kinds (no `dyn`, no level-1
variable), a syntactic condition. That keeps the universe predicative:
`dyn` never contains itself. Level-1 quantification lets programs climb
`dyn, dyn → ★, …` at run time.
-/

namespace BusyLean.Fd

open BusyLean.F.Tm (upRen)

inductive Kind where
  | star : Kind
  | arr : Kind → Kind → Kind
  | kvar : Nat → Kind
  | dvar : Nat → Kind
  | dyn : Kind
  deriving DecidableEq

namespace Kind

/-- Rename level-0 and level-1 kind variables. -/
def ren (ξ₀ ξ₁ : Nat → Nat) : Kind → Kind
  | star => star
  | arr a b => arr (ren ξ₀ ξ₁ a) (ren ξ₀ ξ₁ b)
  | kvar n => kvar (ξ₀ n)
  | dvar n => dvar (ξ₁ n)
  | dyn => dyn

/-- Substitute for level-0 and level-1 kind variables. -/
def subst (σ₀ σ₁ : Nat → Kind) : Kind → Kind
  | star => star
  | arr a b => arr (subst σ₀ σ₁ a) (subst σ₀ σ₁ b)
  | kvar n => σ₀ n
  | dvar n => σ₁ n
  | dyn => dyn

def kcons (K : Kind) (σ : Nat → Kind) : Nat → Kind
  | 0 => K
  | n + 1 => σ n

/-- Dyn-free kinds: no `dyn` and no level-1 variable. -/
def DynFree : Kind → Prop
  | star => True
  | arr a b => DynFree a ∧ DynFree b
  | kvar _ => True
  | dvar _ => False
  | dyn => False

def dynFree : Kind → Bool
  | star => true
  | arr a b => dynFree a && dynFree b
  | kvar _ => true
  | dvar _ => false
  | dyn => false

theorem dynFree_iff : ∀ K : Kind, dynFree K = true ↔ DynFree K
  | star => by simp [dynFree, DynFree]
  | arr a b => by simp [dynFree, DynFree, dynFree_iff a, dynFree_iff b]
  | kvar _ => by simp [dynFree, DynFree]
  | dvar _ => by simp [dynFree, DynFree]
  | dyn => by simp [dynFree, DynFree]

theorem ren_ren : ∀ (K : Kind) (ξ₀ ξ₁ ζ₀ ζ₁ : Nat → Nat),
    ren ξ₀ ξ₁ (ren ζ₀ ζ₁ K) = ren (ξ₀ ∘ ζ₀) (ξ₁ ∘ ζ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, ren_ren a, ren_ren b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl

theorem subst_ren : ∀ (K : Kind) (σ₀ σ₁ : Nat → Kind) (ξ₀ ξ₁ : Nat → Nat),
    subst σ₀ σ₁ (ren ξ₀ ξ₁ K) = subst (σ₀ ∘ ξ₀) (σ₁ ∘ ξ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, subst, subst_ren a, subst_ren b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl

theorem ren_subst : ∀ (K : Kind) (σ₀ σ₁ : Nat → Kind) (ξ₀ ξ₁ : Nat → Nat),
    ren ξ₀ ξ₁ (subst σ₀ σ₁ K) = subst (ren ξ₀ ξ₁ ∘ σ₀) (ren ξ₀ ξ₁ ∘ σ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [ren, subst, ren_subst a, ren_subst b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl

theorem subst_subst : ∀ (K : Kind) (σ₀ σ₁ τ₀ τ₁ : Nat → Kind),
    subst σ₀ σ₁ (subst τ₀ τ₁ K) = subst (subst σ₀ σ₁ ∘ τ₀) (subst σ₀ σ₁ ∘ τ₁) K
  | star, _, _, _, _ => rfl
  | arr a b, _, _, _, _ => by simp only [subst, subst_subst a, subst_subst b]
  | kvar _, _, _, _, _ => rfl
  | dvar _, _, _, _, _ => rfl
  | dyn, _, _, _, _ => rfl

theorem subst_var : ∀ K : Kind, subst kvar dvar K = K
  | star => rfl
  | arr a b => by simp only [subst, subst_var a, subst_var b]
  | kvar _ => rfl
  | dvar _ => rfl
  | dyn => rfl

theorem DynFree.ren {K : Kind} (h : DynFree K) (ξ₀ ξ₁ : Nat → Nat) : DynFree (ren ξ₀ ξ₁ K) := by
  induction K with
  | star => trivial
  | arr a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | kvar _ => trivial
  | dvar _ => exact h.elim
  | dyn => exact h.elim

theorem DynFree.subst {K : Kind} (h : DynFree K) {σ₀ σ₁ : Nat → Kind}
    (hσ : ∀ n, DynFree (σ₀ n)) : DynFree (subst σ₀ σ₁ K) := by
  induction K with
  | star => trivial
  | arr a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | kvar n => exact hσ n
  | dvar _ => exact h.elim
  | dyn => exact h.elim

/-- Shifts for entering a level-0 / level-1 kind binder. -/
def sh₀ (K : Kind) : Kind := ren Nat.succ id K
def sh₁ (K : Kind) : Kind := ren id Nat.succ K

end Kind

inductive Ty where
  | tvar : Nat → Ty
  | arr : Ty → Ty → Ty
  | all : Kind → Ty → Ty
  | lam : Kind → Ty → Ty
  | app : Kind → Ty → Ty → Ty
  | kall0 : Ty → Ty
  | kall1 : Ty → Ty
  | pack : Kind → Ty → Ty
  | unpack : Kind → Ty → Ty
  deriving DecidableEq

namespace Ty

def tren (ξ : Nat → Nat) : Ty → Ty
  | tvar n => tvar (ξ n)
  | arr A B => arr (tren ξ A) (tren ξ B)
  | all k A => all k (tren (upRen ξ) A)
  | lam k A => lam k (tren (upRen ξ) A)
  | app k A B => app k (tren ξ A) (tren ξ B)
  | kall0 A => kall0 (tren ξ A)
  | kall1 A => kall1 (tren ξ A)
  | pack k A => pack k (tren ξ A)
  | unpack k A => unpack k (tren ξ A)

/-- Rename kind variables of both levels. -/
def kren (ξ₀ ξ₁ : Nat → Nat) : Ty → Ty
  | tvar n => tvar n
  | arr A B => arr (kren ξ₀ ξ₁ A) (kren ξ₀ ξ₁ B)
  | all k A => all (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | lam k A => lam (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | app k A B => app (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A) (kren ξ₀ ξ₁ B)
  | kall0 A => kall0 (kren (upRen ξ₀) ξ₁ A)
  | kall1 A => kall1 (kren ξ₀ (upRen ξ₁) A)
  | pack k A => pack (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)
  | unpack k A => unpack (k.ren ξ₀ ξ₁) (kren ξ₀ ξ₁ A)

/-- Lift kind substitutions under a level-0 binder. -/
def kup₀ (σ₀ σ₁ : Nat → Kind) : (Nat → Kind) × (Nat → Kind) :=
  (Kind.kcons (.kvar 0) (fun n => (σ₀ n).sh₀), fun n => (σ₁ n).sh₀)

/-- Lift kind substitutions under a level-1 binder. -/
def kup₁ (σ₀ σ₁ : Nat → Kind) : (Nat → Kind) × (Nat → Kind) :=
  (fun n => (σ₀ n).sh₁, Kind.kcons (.dvar 0) (fun n => (σ₁ n).sh₁))

def ksubst (σ₀ σ₁ : Nat → Kind) : Ty → Ty
  | tvar n => tvar n
  | arr A B => arr (ksubst σ₀ σ₁ A) (ksubst σ₀ σ₁ B)
  | all k A => all (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | lam k A => lam (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | app k A B => app (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A) (ksubst σ₀ σ₁ B)
  | kall0 A => kall0 (ksubst (kup₀ σ₀ σ₁).1 (kup₀ σ₀ σ₁).2 A)
  | kall1 A => kall1 (ksubst (kup₁ σ₀ σ₁).1 (kup₁ σ₀ σ₁).2 A)
  | pack k A => pack (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)
  | unpack k A => unpack (k.subst σ₀ σ₁) (ksubst σ₀ σ₁ A)

def tcons (B : Ty) (σ : Nat → Ty) : Nat → Ty
  | 0 => B
  | n + 1 => σ n

def tup (σ : Nat → Ty) : Nat → Ty := tcons (tvar 0) (fun n => tren Nat.succ (σ n))

def tsubst (σ : Nat → Ty) : Ty → Ty
  | tvar n => σ n
  | arr A B => arr (tsubst σ A) (tsubst σ B)
  | all k A => all k (tsubst (tup σ) A)
  | lam k A => lam k (tsubst (tup σ) A)
  | app k A B => app k (tsubst σ A) (tsubst σ B)
  | kall0 A => kall0 (tsubst (fun n => kren Nat.succ id (σ n)) A)
  | kall1 A => kall1 (tsubst (fun n => kren id Nat.succ (σ n)) A)
  | pack k A => pack k (tsubst σ A)
  | unpack k A => unpack k (tsubst σ A)

def inst (A B : Ty) : Ty := tsubst (tcons B tvar) A

def kinst0 (A : Ty) (K : Kind) : Ty := ksubst (Kind.kcons K .kvar) .dvar A
def kinst1 (A : Ty) (K : Kind) : Ty := ksubst .kvar (Kind.kcons K .dvar) A

def nat : Ty := all .star (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0)))

end Ty

open Ty

/-! ## Kinding -/

abbrev KCtx := Nat → Kind

def kcons (k : Kind) (Δ : KCtx) : KCtx
  | 0 => k
  | n + 1 => Δ n

def KCtx.klift0 (Δ : KCtx) : KCtx := fun n => (Δ n).sh₀
def KCtx.klift1 (Δ : KCtx) : KCtx := fun n => (Δ n).sh₁

inductive Kinded : KCtx → Ty → Kind → Prop where
  | tvar {Δ : KCtx} (n : Nat) : Kinded Δ (tvar n) (Δ n)
  | arr {Δ : KCtx} {A B : Ty} :
      Kinded Δ A .star → Kinded Δ B .star → Kinded Δ (arr A B) .star
  | all {Δ : KCtx} {k : Kind} {A : Ty} :
      Kinded (kcons k Δ) A .star → Kinded Δ (all k A) .star
  | lam {Δ : KCtx} {k₁ k₂ : Kind} {A : Ty} :
      Kinded (kcons k₁ Δ) A k₂ → Kinded Δ (lam k₁ A) (.arr k₁ k₂)
  | app {Δ : KCtx} {k₁ k₂ : Kind} {A B : Ty} :
      Kinded Δ A (.arr k₁ k₂) → Kinded Δ B k₁ → Kinded Δ (app k₁ A B) k₂
  | kall0 {Δ : KCtx} {A : Ty} : Kinded Δ.klift0 A .star → Kinded Δ (kall0 A) .star
  | kall1 {Δ : KCtx} {A : Ty} : Kinded Δ.klift1 A .star → Kinded Δ (kall1 A) .star
  | pack {Δ : KCtx} {k : Kind} {A : Ty} :
      Kinded Δ A k → k.DynFree → Kinded Δ (pack k A) .dyn
  | unpack {Δ : KCtx} {k : Kind} {A : Ty} :
      Kinded Δ A .dyn → k.DynFree → Kinded Δ (unpack k A) k

theorem Kinded.ren {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ {Δ' : KCtx} {ξ : Nat → Nat}, (∀ n, Δ' (ξ n) = Δ n) → Kinded Δ' (tren ξ A) k := by
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

theorem Kinded.kren {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
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

theorem Kinded.ksubst {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ (σ₀ σ₁ : Nat → Kind), (∀ n, (σ₀ n).DynFree) →
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

theorem Kinded.subst {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ {Δ' : KCtx} {σ : Nat → Ty}, (∀ n, Kinded Δ' (σ n) (Δ n)) →
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

theorem Kinded.inst {Δ : KCtx} {k k' : Kind} {A B : Ty}
    (hA : Kinded (kcons k Δ) A k') (hB : Kinded Δ B k) : Kinded Δ (Ty.inst A B) k' :=
  hA.subst fun n => by
    cases n with
    | zero => exact hB
    | succ n => exact Kinded.tvar n

theorem Kinded.kinst0 {Δ : KCtx} {A : Ty} (hA : Kinded Δ.klift0 A .star) {K : Kind}
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

theorem Kinded.kinst1 {Δ : KCtx} {A : Ty} (hA : Kinded Δ.klift1 A .star) (K : Kind) :
    Kinded Δ (Ty.kinst1 A K) .star := by
  have h := hA.ksubst .kvar (Kind.kcons K .dvar) fun _ => trivial
  have e : (fun n => (Δ.klift1 n).subst .kvar (Kind.kcons K .dvar)) = Δ := by
    funext n
    show ((Δ n).ren id Nat.succ).subst _ _ = Δ n
    rw [Kind.subst_ren]
    exact Kind.subst_var (Δ n)
  rw [e] at h
  exact h

theorem Kinded.nat (Δ : KCtx) : Kinded Δ Ty.nat .star :=
  Kinded.all (Kinded.arr (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0))
    (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0)))

/-! ## Type-level reduction -/

inductive TStep : Ty → Ty → Prop where
  | beta (k k' : Kind) (A B : Ty) : TStep (app k (lam k' A) B) (Ty.inst A B)
  | unpackPack (k : Kind) (A : Ty) : k.DynFree → TStep (unpack k (pack k A)) A
  | arrL {A A' : Ty} (B : Ty) : TStep A A' → TStep (arr A B) (arr A' B)
  | arrR (A : Ty) {B B' : Ty} : TStep B B' → TStep (arr A B) (arr A B')
  | all (k : Kind) {A A' : Ty} : TStep A A' → TStep (all k A) (all k A')
  | lam (k : Kind) {A A' : Ty} : TStep A A' → TStep (lam k A) (lam k A')
  | appL (k : Kind) {A A' : Ty} (B : Ty) : TStep A A' → TStep (app k A B) (app k A' B)
  | appR (k : Kind) (A : Ty) {B B' : Ty} : TStep B B' → TStep (app k A B) (app k A B')
  | kall0 {A A' : Ty} : TStep A A' → TStep (kall0 A) (kall0 A')
  | kall1 {A A' : Ty} : TStep A A' → TStep (kall1 A) (kall1 A')
  | pack (k : Kind) {A A' : Ty} : TStep A A' → TStep (pack k A) (pack k A')
  | unpack (k : Kind) {A A' : Ty} : TStep A A' → TStep (unpack k A) (unpack k A')

inductive TSteps : Ty → Ty → Prop where
  | refl (A : Ty) : TSteps A A
  | step {A B C : Ty} : TStep A B → TSteps B C → TSteps A C

def TJoin (A B : Ty) : Prop := ∃ C, TSteps A C ∧ TSteps B C

theorem TSteps.join_left {A B : Ty} (s : TSteps A B) : TJoin A B := ⟨B, s, TSteps.refl B⟩

theorem TJoin.symm {A B : Ty} (j : TJoin A B) : TJoin B A := by
  obtain ⟨C, h₁, h₂⟩ := j
  exact ⟨C, h₂, h₁⟩

theorem Kinded.step {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) {B : Ty}
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

theorem Kinded.steps {Δ : KCtx} {A B : Ty} {k : Kind} (h : Kinded Δ A k) (s : TSteps A B) :
    Kinded Δ B k := by
  induction s with
  | refl => exact h
  | step s _ ih => exact ih (h.step s)

/-! ## A sound, fuel-bounded type normalizer -/

def tappCong (k : Kind) (A B : Ty) (sA sB : Option Ty) : Option Ty :=
  match sA with
  | some A' => some (app k A' B)
  | none => sB.map (app k A)

def tappStep (k : Kind) (A B : Ty) (sA sB : Option Ty) : Option Ty :=
  match A with
  | lam _ A₀ => some (Ty.inst A₀ B)
  | _ => tappCong k A B sA sB

/-- The unpack-of-pack redex, when the kinds agree and are dyn-free. -/
def unpackRedex (k : Kind) (A : Ty) : Option Ty :=
  match A with
  | pack k' A₀ => if k' = k ∧ k.dynFree = true then some A₀ else none
  | _ => none

def tstep : Ty → Option Ty
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

theorem tappCong_sound {k : Kind} {A B C : Ty} {sA sB : Option Ty}
    (hA : ∀ A', sA = some A' → TStep A A') (hB : ∀ B', sB = some B' → TStep B B')
    (h : tappCong k A B sA sB = some C) : TStep (app k A B) C := by
  unfold tappCong at h
  cases sA with
  | some A' => cases h; exact TStep.appL _ _ (hA A' rfl)
  | none =>
      cases sB with
      | none => cases h
      | some B' => cases h; exact TStep.appR _ _ (hB B' rfl)

theorem tappStep_sound {k : Kind} {A B C : Ty} {sA sB : Option Ty}
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

theorem unpackRedex_sound {k : Kind} {A B : Ty} (h : unpackRedex k A = some B) :
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

theorem tstep_sound : ∀ {A B : Ty}, tstep A = some B → TStep A B
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

def tnf : Nat → Ty → Ty
  | 0, A => A
  | fuel + 1, A =>
      match tstep A with
      | some B => tnf fuel B
      | none => A

theorem tnf_steps : ∀ (fuel : Nat) (A : Ty), TSteps A (tnf fuel A)
  | 0, A => TSteps.refl A
  | fuel + 1, A => by
      simp only [tnf]
      cases h : tstep A with
      | none => exact TSteps.refl A
      | some B => exact TSteps.step (tstep_sound h) (tnf_steps fuel B)

theorem tjoin_of_tnf {fuel : Nat} {A B : Ty} (h : tnf fuel A = tnf fuel B) : TJoin A B :=
  ⟨tnf fuel A, tnf_steps fuel A, h ▸ tnf_steps fuel B⟩

/-! ## Kind inference -/

open BusyLean.Fw (nth?)

def kctxOf (Δ : List Kind) : KCtx := fun n => (nth? Δ n).getD .star

theorem kctxOf_cons (k : Kind) (Δ : List Kind) : kctxOf (k :: Δ) = kcons k (kctxOf Δ) := by
  funext n; cases n <;> rfl

theorem nth?_map {α β : Type} (g : α → β) : ∀ (l : List α) (n : Nat),
    nth? (l.map g) n = (nth? l n).map g
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => nth?_map g l n

theorem kctxOf_klift0 (Δ : List Kind) : kctxOf (Δ.map Kind.sh₀) = (kctxOf Δ).klift0 := by
  funext n
  show (nth? (Δ.map Kind.sh₀) n).getD .star = ((nth? Δ n).getD .star).sh₀
  rw [nth?_map]
  cases nth? Δ n <;> rfl

theorem kctxOf_klift1 (Δ : List Kind) : kctxOf (Δ.map Kind.sh₁) = (kctxOf Δ).klift1 := by
  funext n
  show (nth? (Δ.map Kind.sh₁) n).getD .star = ((nth? Δ n).getD .star).sh₁
  rw [nth?_map]
  cases nth? Δ n <;> rfl

def inferKind : List Kind → Ty → Option Kind
  | Δ, tvar n => nth? Δ n
  | Δ, arr A B =>
      match inferKind Δ A, inferKind Δ B with
      | some .star, some .star => some .star
      | _, _ => none
  | Δ, all k A =>
      match inferKind (k :: Δ) A with
      | some .star => some .star
      | _ => none
  | Δ, lam k A => (inferKind (k :: Δ) A).map (Kind.arr k)
  | Δ, app k A B =>
      match inferKind Δ A, inferKind Δ B with
      | some (.arr k₁ k₂), some k' => if k₁ = k ∧ k' = k then some k₂ else none
      | _, _ => none
  | Δ, kall0 A =>
      match inferKind (Δ.map Kind.sh₀) A with
      | some .star => some .star
      | _ => none
  | Δ, kall1 A =>
      match inferKind (Δ.map Kind.sh₁) A with
      | some .star => some .star
      | _ => none
  | Δ, pack k A =>
      match inferKind Δ A with
      | some k' => if k' = k ∧ k.dynFree = true then some .dyn else none
      | none => none
  | Δ, unpack k A =>
      match inferKind Δ A with
      | some .dyn => if k.dynFree = true then some k else none
      | _ => none

/-- The kind-inference cases that only check a `★` result. -/
theorem star_of_match {o : Option Kind} {k : Kind}
    (h : (match o with
      | some .star => some Kind.star
      | _ => none) = some k) : o = some .star ∧ k = .star := by
  match o, h with
  | some .star, h => cases h; exact ⟨rfl, rfl⟩

theorem inferKind_sound : ∀ (A : Ty) {Δ : List Kind} {k : Kind},
    inferKind Δ A = some k → Kinded (kctxOf Δ) A k
  | tvar n, Δ, k, h => by
      have e : kctxOf Δ n = k := by
        show (nth? Δ n).getD .star = k
        rw [show nth? Δ n = some k from h]; rfl
      rw [← e]; exact Kinded.tvar n
  | arr A B, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind Δ A with
      | none => rw [hA] at h; cases h
      | some kA =>
          cases hB : inferKind Δ B with
          | none => rw [hA, hB] at h; cases kA <;> cases h
          | some kB =>
              rw [hA, hB] at h
              cases kA <;> cases kB <;> cases h
              exact Kinded.arr (inferKind_sound A hA) (inferKind_sound B hB)
  | all k' A, Δ, k, h => by
      simp only [inferKind] at h
      obtain ⟨hA, rfl⟩ := star_of_match h
      have ih := inferKind_sound A hA
      rw [kctxOf_cons] at ih
      exact Kinded.all ih
  | lam k' A, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind (k' :: Δ) A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          cases h
          have ih := inferKind_sound A hA
          rw [kctxOf_cons] at ih
          exact Kinded.lam ih
  | app k' A B, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind Δ A with
      | none => rw [hA] at h; cases h
      | some kA =>
          cases hB : inferKind Δ B with
          | none => rw [hA, hB] at h; cases kA <;> cases h
          | some kB =>
              rw [hA, hB] at h
              cases kA with
              | arr k₁ k₂ =>
                  change (if k₁ = k' ∧ kB = k' then some k₂ else none) = some k at h
                  by_cases e : k₁ = k' ∧ kB = k'
                  · rw [ite_eq_left e] at h
                    cases h
                    obtain ⟨rfl, rfl⟩ := e
                    exact Kinded.app (inferKind_sound A hA) (inferKind_sound B hB)
                  · rw [ite_eq_right e] at h; cases h
              | star => cases h
              | kvar _ => cases h
              | dvar _ => cases h
              | dyn => cases h
  | kall0 A, Δ, k, h => by
      simp only [inferKind] at h
      obtain ⟨hA, rfl⟩ := star_of_match h
      have ih := inferKind_sound A hA
      rw [kctxOf_klift0] at ih
      exact Kinded.kall0 ih
  | kall1 A, Δ, k, h => by
      simp only [inferKind] at h
      obtain ⟨hA, rfl⟩ := star_of_match h
      have ih := inferKind_sound A hA
      rw [kctxOf_klift1] at ih
      exact Kinded.kall1 ih
  | pack k' A, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind Δ A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          change (if kA = k' ∧ k'.dynFree = true then some Kind.dyn else none) = some k at h
          by_cases e : kA = k' ∧ k'.dynFree = true
          · rw [ite_eq_left e] at h
            cases h
            obtain ⟨rfl, hk⟩ := e
            exact Kinded.pack (inferKind_sound A hA) ((Kind.dynFree_iff _).1 hk)
          · rw [ite_eq_right e] at h; cases h
  | unpack k' A, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind Δ A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          cases kA with
          | dyn =>
              change (if k'.dynFree = true then some k' else none) = some k at h
              by_cases e : k'.dynFree = true
              · rw [ite_eq_left e] at h
                cases h
                exact Kinded.unpack (inferKind_sound A hA) ((Kind.dynFree_iff _).1 e)
              · rw [ite_eq_right e] at h; cases h
          | star => cases h
          | arr _ _ => cases h
          | kvar _ => cases h
          | dvar _ => cases h

end BusyLean.Fd
