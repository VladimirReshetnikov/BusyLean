import BusyLean.SystemFw.Types

/-!
# System Fω with kind polymorphism: syntax, kinding, type-level β

Kinds now contain *kind variables* (`kvar`), and types may quantify over kinds
(`kall A`, i.e. `∀κ. A`, a type of kind `★`). Kinds have no binders, so kind
variables always range over closed kinds. In pure type system terms the new
rule is (△, ★) without (△, □); the dangerous rule (△, □) behind Girard's
paradox is absent.

The interesting consequence is that a single program can work at kinds of
*unbounded* order chosen at run time. A step `∀κ. B κ → B (κ → ★)`, iterated
through existential packages `∃κ. B κ`, climbs one order per iteration.
-/

namespace BusyLean.Fk

open BusyLean.F.Tm (upRen)

inductive Kind where
  | star : Kind
  | arr : Kind → Kind → Kind
  | kvar : Nat → Kind
  deriving DecidableEq

namespace Kind

def kren (ξ : Nat → Nat) : Kind → Kind
  | star => star
  | arr k₁ k₂ => arr (kren ξ k₁) (kren ξ k₂)
  | kvar n => kvar (ξ n)

def ksubst (κs : Nat → Kind) : Kind → Kind
  | star => star
  | arr k₁ k₂ => arr (ksubst κs k₁) (ksubst κs k₂)
  | kvar n => κs n

def kcons (K : Kind) (κs : Nat → Kind) : Nat → Kind
  | 0 => K
  | n + 1 => κs n

/-- Lift a kind substitution under a kind binder. -/
def kup (κs : Nat → Kind) : Nat → Kind := kcons (kvar 0) (fun n => kren Nat.succ (κs n))

theorem kren_kren : ∀ (K : Kind) (ξ ζ : Nat → Nat), kren ξ (kren ζ K) = kren (ξ ∘ ζ) K
  | star, _, _ => rfl
  | arr k₁ k₂, ξ, ζ => by simp only [kren, kren_kren k₁, kren_kren k₂]
  | kvar _, _, _ => rfl

theorem ksubst_kren : ∀ (K : Kind) (κs : Nat → Kind) (ξ : Nat → Nat),
    ksubst κs (kren ξ K) = ksubst (κs ∘ ξ) K
  | star, _, _ => rfl
  | arr k₁ k₂, κs, ξ => by simp only [kren, ksubst, ksubst_kren k₁, ksubst_kren k₂]
  | kvar _, _, _ => rfl

theorem kren_ksubst : ∀ (K : Kind) (κs : Nat → Kind) (ξ : Nat → Nat),
    kren ξ (ksubst κs K) = ksubst (kren ξ ∘ κs) K
  | star, _, _ => rfl
  | arr k₁ k₂, κs, ξ => by simp only [kren, ksubst, kren_ksubst k₁, kren_ksubst k₂]
  | kvar _, _, _ => rfl

/-- Lifting commutes with shifting. -/
theorem kren_upRen_succ (ξ : Nat → Nat) (K : Kind) :
    kren (upRen ξ) (kren Nat.succ K) = kren Nat.succ (kren ξ K) := by
  rw [kren_kren, kren_kren]; rfl

theorem ksubst_kup_succ (κs : Nat → Kind) (K : Kind) :
    ksubst (kup κs) (kren Nat.succ K) = kren Nat.succ (ksubst κs K) := by
  rw [ksubst_kren, kren_ksubst]; rfl

/-- Closed semantic kinds are Fω's kinds; evaluate under a kind valuation. -/
def evalK (θ : Nat → Fw.Kind) : Kind → Fw.Kind
  | star => .star
  | arr k₁ k₂ => .arr (evalK θ k₁) (evalK θ k₂)
  | kvar n => θ n

def θcons (K : Fw.Kind) (θ : Nat → Fw.Kind) : Nat → Fw.Kind
  | 0 => K
  | n + 1 => θ n

theorem evalK_kren : ∀ (K : Kind) (θ : Nat → Fw.Kind) (ξ : Nat → Nat),
    evalK θ (kren ξ K) = evalK (θ ∘ ξ) K
  | star, _, _ => rfl
  | arr k₁ k₂, θ, ξ => by simp only [kren, evalK, evalK_kren k₁, evalK_kren k₂]
  | kvar _, _, _ => rfl

theorem evalK_ksubst : ∀ (K : Kind) (θ : Nat → Fw.Kind) (κs : Nat → Kind),
    evalK θ (ksubst κs K) = evalK (fun n => evalK θ (κs n)) K
  | star, _, _ => rfl
  | arr k₁ k₂, θ, κs => by simp only [ksubst, evalK, evalK_ksubst k₁, evalK_ksubst k₂]
  | kvar _, _, _ => rfl

theorem evalK_succ (K : Kind) (K' : Fw.Kind) (θ : Nat → Fw.Kind) :
    evalK (θcons K' θ) (kren Nat.succ K) = evalK θ K := by
  rw [evalK_kren]; rfl

end Kind

inductive Ty where
  | tvar : Nat → Ty
  | arr : Ty → Ty → Ty
  | all : Kind → Ty → Ty
  | lam : Kind → Ty → Ty
  | app : Kind → Ty → Ty → Ty
  | kall : Ty → Ty
  deriving DecidableEq

namespace Ty

/-- Rename type variables. -/
def tren (ξ : Nat → Nat) : Ty → Ty
  | tvar n => tvar (ξ n)
  | arr A B => arr (tren ξ A) (tren ξ B)
  | all k A => all k (tren (upRen ξ) A)
  | lam k A => lam k (tren (upRen ξ) A)
  | app k A B => app k (tren ξ A) (tren ξ B)
  | kall A => kall (tren ξ A)

/-- Rename kind variables (inside every kind annotation). -/
def kren (ξ : Nat → Nat) : Ty → Ty
  | tvar n => tvar n
  | arr A B => arr (kren ξ A) (kren ξ B)
  | all k A => all (k.kren ξ) (kren ξ A)
  | lam k A => lam (k.kren ξ) (kren ξ A)
  | app k A B => app (k.kren ξ) (kren ξ A) (kren ξ B)
  | kall A => kall (kren (upRen ξ) A)

/-- Substitute kinds for kind variables. -/
def ksubst (κs : Nat → Kind) : Ty → Ty
  | tvar n => tvar n
  | arr A B => arr (ksubst κs A) (ksubst κs B)
  | all k A => all (k.ksubst κs) (ksubst κs A)
  | lam k A => lam (k.ksubst κs) (ksubst κs A)
  | app k A B => app (k.ksubst κs) (ksubst κs A) (ksubst κs B)
  | kall A => kall (ksubst (Kind.kup κs) A)

def tcons (B : Ty) (σ : Nat → Ty) : Nat → Ty
  | 0 => B
  | n + 1 => σ n

/-- Lift a type substitution under a type binder. -/
def tup (σ : Nat → Ty) : Nat → Ty := tcons (tvar 0) (fun n => tren Nat.succ (σ n))

/-- Lift a type substitution under a kind binder. -/
def tkup (σ : Nat → Ty) : Nat → Ty := fun n => kren Nat.succ (σ n)

def tsubst (σ : Nat → Ty) : Ty → Ty
  | tvar n => σ n
  | arr A B => arr (tsubst σ A) (tsubst σ B)
  | all k A => all k (tsubst (tup σ) A)
  | lam k A => lam k (tsubst (tup σ) A)
  | app k A B => app k (tsubst σ A) (tsubst σ B)
  | kall A => kall (tsubst (tkup σ) A)

/-- `A[B/0]` for a type variable. -/
def inst (A B : Ty) : Ty := tsubst (tcons B tvar) A

/-- `A[K/0]` for a kind variable. -/
def kinst (A : Ty) (K : Kind) : Ty := ksubst (Kind.kcons K Kind.kvar) A

def nat : Ty := all .star (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0)))

end Ty

open Ty

/-! ## Kinding -/

abbrev KCtx := Nat → Kind

def kcons (k : Kind) (Δ : KCtx) : KCtx
  | 0 => k
  | n + 1 => Δ n

/-- Shift the kinds of a type-variable context when entering a kind binder. -/
def KCtx.klift (Δ : KCtx) : KCtx := fun n => (Δ n).kren Nat.succ

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
  | kall {Δ : KCtx} {A : Ty} : Kinded Δ.klift A .star → Kinded Δ (kall A) .star

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
  | kall _ ih =>
      intro Δ' ξ hξ
      exact Kinded.kall (ih fun n => by simp [KCtx.klift, hξ])

theorem Kinded.kren {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ (ξ : Nat → Nat), Kinded (fun n => (Δ n).kren ξ) (Ty.kren ξ A) (k.kren ξ) := by
  induction h with
  | tvar n => intro ξ; exact Kinded.tvar n
  | arr _ _ ih₁ ih₂ => intro ξ; exact Kinded.arr (ih₁ ξ) (ih₂ ξ)
  | @all Δ k A _ ih =>
      intro ξ
      refine Kinded.all ?_
      have e : (fun n => (kcons k Δ n).kren ξ) = kcons (k.kren ξ) (fun n => (Δ n).kren ξ) := by
        funext n; cases n <;> rfl
      have := ih ξ
      rw [e] at this
      exact this
  | @lam Δ k₁ k₂ A _ ih =>
      intro ξ
      refine Kinded.lam ?_
      have e : (fun n => (kcons k₁ Δ n).kren ξ) =
          kcons (k₁.kren ξ) (fun n => (Δ n).kren ξ) := by
        funext n; cases n <;> rfl
      have := ih ξ
      rw [e] at this
      exact this
  | app _ _ ih₁ ih₂ => intro ξ; exact Kinded.app (ih₁ ξ) (ih₂ ξ)
  | @kall Δ A _ ih =>
      intro ξ
      refine Kinded.kall ?_
      have := ih (upRen ξ)
      have e : (fun n => (Δ.klift n).kren (upRen ξ)) =
          KCtx.klift (fun n => (Δ n).kren ξ) := by
        funext n
        exact Kind.kren_upRen_succ ξ (Δ n)
      rw [e] at this
      exact this

theorem Kinded.ksubst {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ (κs : Nat → Kind),
      Kinded (fun n => (Δ n).ksubst κs) (Ty.ksubst κs A) (k.ksubst κs) := by
  induction h with
  | tvar n => intro κs; exact Kinded.tvar n
  | arr _ _ ih₁ ih₂ => intro κs; exact Kinded.arr (ih₁ κs) (ih₂ κs)
  | @all Δ k A _ ih =>
      intro κs
      refine Kinded.all ?_
      have e : (fun n => (kcons k Δ n).ksubst κs) =
          kcons (k.ksubst κs) (fun n => (Δ n).ksubst κs) := by
        funext n; cases n <;> rfl
      have := ih κs
      rw [e] at this
      exact this
  | @lam Δ k₁ k₂ A _ ih =>
      intro κs
      refine Kinded.lam ?_
      have e : (fun n => (kcons k₁ Δ n).ksubst κs) =
          kcons (k₁.ksubst κs) (fun n => (Δ n).ksubst κs) := by
        funext n; cases n <;> rfl
      have := ih κs
      rw [e] at this
      exact this
  | app _ _ ih₁ ih₂ => intro κs; exact Kinded.app (ih₁ κs) (ih₂ κs)
  | @kall Δ A _ ih =>
      intro κs
      refine Kinded.kall ?_
      have := ih (Kind.kup κs)
      have e : (fun n => (Δ.klift n).ksubst (Kind.kup κs)) =
          KCtx.klift (fun n => (Δ n).ksubst κs) := by
        funext n
        exact Kind.ksubst_kup_succ κs (Δ n)
      rw [e] at this
      exact this

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
  | @kall Δ A _ ih =>
      intro Δ' σ hσ
      exact Kinded.kall (ih fun n => (hσ n).kren Nat.succ)

theorem Kinded.inst {Δ : KCtx} {k k' : Kind} {A B : Ty}
    (hA : Kinded (kcons k Δ) A k') (hB : Kinded Δ B k) : Kinded Δ (Ty.inst A B) k' :=
  hA.subst fun n => by
    cases n with
    | zero => exact hB
    | succ n => exact Kinded.tvar n

theorem Kind.ksubst_succ_cons (K : Kind) :
    ∀ k : Kind, k.ksubst (Kind.kcons K Kind.kvar ∘ Nat.succ) = k
  | .star => rfl
  | .arr k₁ k₂ => by
      simp only [Kind.ksubst, Kind.ksubst_succ_cons K k₁, Kind.ksubst_succ_cons K k₂]
  | .kvar _ => rfl

/-- Kind instantiation preserves kinding of `★`-types. -/
theorem Kinded.kinst {Δ : KCtx} {A : Ty} (hA : Kinded Δ.klift A .star) (K : Kind) :
    Kinded Δ (Ty.kinst A K) .star := by
  have h := hA.ksubst (Kind.kcons K Kind.kvar)
  have e : (fun n => (Δ.klift n).ksubst (Kind.kcons K Kind.kvar)) = Δ := by
    funext n
    show ((Δ n).kren Nat.succ).ksubst _ = Δ n
    rw [Kind.ksubst_kren]
    exact Kind.ksubst_succ_cons K (Δ n)
  rw [e] at h
  exact h

theorem Kinded.nat (Δ : KCtx) : Kinded Δ Ty.nat .star :=
  Kinded.all (Kinded.arr (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0))
    (Kinded.arr (Kinded.tvar 0) (Kinded.tvar 0)))

/-! ## Type-level β-reduction -/

inductive TStep : Ty → Ty → Prop where
  | beta (k k' : Kind) (A B : Ty) : TStep (app k (lam k' A) B) (Ty.inst A B)
  | arrL {A A' : Ty} (B : Ty) : TStep A A' → TStep (arr A B) (arr A' B)
  | arrR (A : Ty) {B B' : Ty} : TStep B B' → TStep (arr A B) (arr A B')
  | all (k : Kind) {A A' : Ty} : TStep A A' → TStep (all k A) (all k A')
  | lam (k : Kind) {A A' : Ty} : TStep A A' → TStep (lam k A) (lam k A')
  | appL (k : Kind) {A A' : Ty} (B : Ty) : TStep A A' → TStep (app k A B) (app k A' B)
  | appR (k : Kind) (A : Ty) {B B' : Ty} : TStep B B' → TStep (app k A B) (app k A B')
  | kall {A A' : Ty} : TStep A A' → TStep (kall A) (kall A')

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
  | arrL _ _ ih => cases h with | arr h₁ h₂ => exact Kinded.arr (ih h₁) h₂
  | arrR _ _ ih => cases h with | arr h₁ h₂ => exact Kinded.arr h₁ (ih h₂)
  | all _ _ ih => cases h with | all h₁ => exact Kinded.all (ih h₁)
  | lam _ _ ih => cases h with | lam h₁ => exact Kinded.lam (ih h₁)
  | appL _ _ _ ih => cases h with | app h₁ h₂ => exact Kinded.app (ih h₁) h₂
  | appR _ _ _ ih => cases h with | app h₁ h₂ => exact Kinded.app h₁ (ih h₂)
  | kall _ ih => cases h with | kall h₁ => exact Kinded.kall (ih h₁)

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

def tstep : Ty → Option Ty
  | tvar _ => none
  | arr A B =>
      match tstep A with
      | some A' => some (arr A' B)
      | none => (tstep B).map (arr A)
  | all k A => (tstep A).map (all k)
  | lam k A => (tstep A).map (lam k)
  | app k A B => tappStep k A B (tstep A) (tstep B)
  | kall A => (tstep A).map kall

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
  | kall _ => exact tappCong_sound hA hB h

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
  | kall A, C, h => by
      simp only [tstep] at h
      cases hA : tstep A with
      | none => rw [hA] at h; cases h
      | some A' => rw [hA] at h; cases h; exact TStep.kall (tstep_sound hA)

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

theorem kctxOf_klift (Δ : List Kind) :
    kctxOf (Δ.map (Kind.kren Nat.succ)) = (kctxOf Δ).klift := by
  funext n
  show (nth? (Δ.map (Kind.kren Nat.succ)) n).getD .star = ((nth? Δ n).getD .star).kren Nat.succ
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
  | Δ, kall A =>
      match inferKind (Δ.map (Kind.kren Nat.succ)) A with
      | some .star => some .star
      | _ => none

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
              cases kA with
              | arr _ _ => cases h
              | kvar _ => cases h
              | star =>
                  cases kB with
                  | arr _ _ => cases h
                  | kvar _ => cases h
                  | star =>
                      cases h
                      exact Kinded.arr (inferKind_sound A hA) (inferKind_sound B hB)
  | all k' A, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind (k' :: Δ) A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          cases kA with
          | arr _ _ => cases h
          | kvar _ => cases h
          | star =>
              cases h
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
              | star => cases h
              | kvar _ => cases h
              | arr k₁ k₂ =>
                  change (if k₁ = k' ∧ kB = k' then some k₂ else none) = some k at h
                  by_cases e : k₁ = k' ∧ kB = k'
                  · rw [ite_eq_left e] at h
                    cases h
                    obtain ⟨rfl, rfl⟩ := e
                    exact Kinded.app (inferKind_sound A hA) (inferKind_sound B hB)
                  · rw [ite_eq_right e] at h; cases h
  | kall A, Δ, k, h => by
      simp only [inferKind] at h
      cases hA : inferKind (Δ.map (Kind.kren Nat.succ)) A with
      | none => rw [hA] at h; cases h
      | some kA =>
          rw [hA] at h
          cases kA with
          | arr _ _ => cases h
          | kvar _ => cases h
          | star =>
              cases h
              have ih := inferKind_sound A hA
              rw [kctxOf_klift] at ih
              exact Kinded.kall ih

end BusyLean.Fk
