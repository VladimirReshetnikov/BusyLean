/-!
# Untyped λ-terms with an oracle constant

The computational core of Contender 7 is untyped λ-calculus with de Bruijn
indices, plus the oracle constant `orc` and three inert tree constructors `con k`. System F types are *erased*
before normalization, so all reduction happens here.

Substitutions are total functions `ℕ → Tm` (parallel substitution in the style
of Autosubst). Renamings are functions `ℕ → ℕ`.
-/

namespace BusyLean.FT

inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  | orc : Tm
  /-- Tree constructors: `con 0` zero, `con 1` successor, `con 2` limit. -/
  | con : Nat → Tm

namespace Tm

/-- Lift a renaming under a binder. -/
def upRen (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

def ren (ξ : Nat → Nat) : Tm → Tm
  | var n => var (ξ n)
  | app t u => app (ren ξ t) (ren ξ u)
  | lam t => lam (ren (upRen ξ) t)
  | orc => orc
  | con k => con k

/-- `cons a σ` maps `0 ↦ a` and `n+1 ↦ σ n`. -/
def cons (a : Tm) (σ : Nat → Tm) : Nat → Tm
  | 0 => a
  | n + 1 => σ n

/-- Lift a substitution under a binder. -/
def up (σ : Nat → Tm) : Nat → Tm := cons (var 0) (fun n => ren Nat.succ (σ n))

def subst (σ : Nat → Tm) : Tm → Tm
  | var n => σ n
  | app t u => app (subst σ t) (subst σ u)
  | lam t => lam (subst (up σ) t)
  | orc => orc
  | con k => con k

/-! ## Renaming lemmas -/

theorem upRen_comp (ξ ζ : Nat → Nat) : upRen ξ ∘ upRen ζ = upRen (ξ ∘ ζ) := by
  funext n; cases n <;> rfl

theorem ren_ren : ∀ (t : Tm) (ξ ζ : Nat → Nat), ren ξ (ren ζ t) = ren (ξ ∘ ζ) t
  | var _, _, _ => rfl
  | app t u, ξ, ζ => by simp only [ren, ren_ren t, ren_ren u]
  | lam t, ξ, ζ => by simp only [ren, ren_ren t, upRen_comp]
  | orc, _, _ => rfl
  | con _, _, _ => rfl

theorem upRen_id : upRen id = id := by funext n; cases n <;> rfl

theorem ren_id : ∀ t : Tm, ren id t = t
  | var _ => rfl
  | app t u => by simp only [ren, ren_id t, ren_id u]
  | lam t => by simp only [ren, upRen_id, ren_id t]
  | orc => rfl
  | con _ => rfl

/-! ## Renaming as substitution -/

theorem up_var_ren (ξ : Nat → Nat) : up (var ∘ ξ) = var ∘ upRen ξ := by
  funext n; cases n <;> rfl

theorem ren_eq_subst : ∀ (t : Tm) (ξ : Nat → Nat), ren ξ t = subst (var ∘ ξ) t
  | var _, _ => rfl
  | app t u, ξ => by simp only [ren, subst, ren_eq_subst t, ren_eq_subst u]
  | lam t, ξ => by simp only [ren, subst, ren_eq_subst t, up_var_ren]
  | orc, _ => rfl
  | con _, _ => rfl

/-! ## Interaction of substitution and renaming -/

theorem up_comp_upRen (σ : Nat → Tm) (ξ : Nat → Nat) : up σ ∘ upRen ξ = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem subst_ren : ∀ (t : Tm) (σ : Nat → Tm) (ξ : Nat → Nat),
    subst σ (ren ξ t) = subst (σ ∘ ξ) t
  | var _, _, _ => rfl
  | app t u, σ, ξ => by simp only [ren, subst, subst_ren t, subst_ren u]
  | lam t, σ, ξ => by simp only [ren, subst, subst_ren t, up_comp_upRen]
  | orc, _, _ => rfl
  | con _, _, _ => rfl

theorem upRen_comp_up (σ : Nat → Tm) (ξ : Nat → Nat) :
    ren (upRen ξ) ∘ up σ = up (ren ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show ren (upRen ξ) (ren Nat.succ (σ n)) = ren Nat.succ (ren ξ (σ n))
      rw [ren_ren, ren_ren]
      rfl

theorem ren_subst : ∀ (t : Tm) (σ : Nat → Tm) (ξ : Nat → Nat),
    ren ξ (subst σ t) = subst (ren ξ ∘ σ) t
  | var _, _, _ => rfl
  | app t u, σ, ξ => by simp only [ren, subst, ren_subst t, ren_subst u]
  | lam t, σ, ξ => by simp only [ren, subst, ren_subst t, upRen_comp_up]
  | orc, _, _ => rfl
  | con _, _, _ => rfl

/-! ## Composition of substitutions -/

theorem up_comp (σ τ : Nat → Tm) : subst (up σ) ∘ up τ = up (subst σ ∘ τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show subst (up σ) (ren Nat.succ (τ n)) = ren Nat.succ (subst σ (τ n))
      rw [subst_ren, ren_subst]
      rfl

theorem subst_subst : ∀ (t : Tm) (σ τ : Nat → Tm),
    subst σ (subst τ t) = subst (subst σ ∘ τ) t
  | var _, _, _ => rfl
  | app t u, σ, τ => by simp only [subst, subst_subst t, subst_subst u]
  | lam t, σ, τ => by simp only [subst, subst_subst t, up_comp]
  | orc, _, _ => rfl
  | con _, _, _ => rfl

theorem up_var : up var = var := by funext n; cases n <;> rfl

theorem subst_var : ∀ t : Tm, subst var t = t
  | var _ => rfl
  | app t u => by simp only [subst, subst_var t, subst_var u]
  | lam t => by simp only [subst, up_var, subst_var t]
  | orc => rfl
  | con _ => rfl

/-- The β-substitution commutes with a lifted substitution. -/
theorem subst_beta (b a : Tm) (σ : Nat → Tm) :
    subst (cons a var) (subst (up σ) b) = subst (cons a σ) b := by
  rw [subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show subst (cons a var) (ren Nat.succ (σ n)) = σ n
      rw [subst_ren]
      exact subst_var (σ n)

/-- Substituting into a β-redex's result. -/
theorem subst_cons_comm (b a : Tm) (σ : Nat → Tm) :
    subst σ (subst (cons a var) b) = subst (cons (subst σ a) var) (subst (up σ) b) := by
  rw [subst_beta, subst_subst]
  congr 1
  funext n
  cases n <;> rfl

/-! ## Church numerals -/

/-- `f (f (… (f x)))` with `f = var 1`, `x = var 0`. -/
def iterApp : Nat → Tm
  | 0 => var 0
  | n + 1 => app (var 1) (iterApp n)

/-- The Church numeral `λf. λx. fⁿ x`. -/
def num (n : Nat) : Tm := lam (lam (iterApp n))

theorem subst_iterApp (σ : Nat → Tm) :
    ∀ n, subst (up (up σ)) (iterApp n) = iterApp n
  | 0 => rfl
  | n + 1 => by
      show app (up (up σ) 1) (subst (up (up σ)) (iterApp n)) = _
      rw [subst_iterApp σ n]
      rfl

/-- Numerals are closed. -/
theorem subst_num (σ : Nat → Tm) (n : Nat) : subst σ (num n) = num n := by
  show lam (lam (subst (up (up σ)) (iterApp n))) = _
  rw [subst_iterApp]
  rfl

/-- Recognize the body of a numeral. -/
def iterApp? : Tm → Option Nat
  | var 0 => some 0
  | app (var 1) t => (iterApp? t).map Nat.succ
  | _ => none

/-- Recognize a Church numeral in normal form. -/
def num? : Tm → Option Nat
  | lam (lam t) => iterApp? t
  | _ => none

theorem iterApp?_spec : ∀ {t : Tm} {n : Nat}, iterApp? t = some n → t = iterApp n
  | var 0, n, h => by
      simp only [iterApp?, Option.some.injEq] at h
      subst h; rfl
  | app (var 1) t, n, h => by
      simp only [iterApp?] at h
      cases ht : iterApp? t with
      | none => rw [ht] at h; cases h
      | some m =>
          rw [ht] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rw [iterApp?_spec ht]
          rfl
  | var (_ + 2), _, h => by simp [iterApp?] at h
  | var 1, _, h => by simp [iterApp?] at h
  | app (var 0) _, _, h => by simp [iterApp?] at h
  | app (var (_ + 2)) _, _, h => by simp [iterApp?] at h
  | app (app _ _) _, _, h => by simp [iterApp?] at h
  | app (lam _) _, _, h => by simp [iterApp?] at h
  | app orc _, _, h => by simp [iterApp?] at h
  | app (con _) _, _, h => by simp [iterApp?] at h
  | lam _, _, h => by simp [iterApp?] at h
  | orc, _, h => by simp [iterApp?] at h
  | con _, _, h => by simp [iterApp?] at h

theorem num?_spec {t : Tm} {n : Nat} (h : num? t = some n) : t = num n := by
  match t, h with
  | lam (lam b), h => rw [iterApp?_spec h]; rfl

theorem iterApp?_iterApp : ∀ n, iterApp? (iterApp n) = some n
  | 0 => rfl
  | n + 1 => by
      show (iterApp? (iterApp n)).map Nat.succ = _
      rw [iterApp?_iterApp n]
      rfl

theorem num?_num (n : Nat) : num? (num n) = some n := iterApp?_iterApp n

end Tm
end BusyLean.FT
