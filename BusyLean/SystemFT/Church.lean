import BusyLean.SystemFT.Types

/-!
# Church-style System F terms and type inference

Programs are written Church-style, with type annotations on λ and explicit
type abstraction and application, so that type checking is decidable. `infer`
is a type inferrer. Its soundness theorem connects it to the Curry-style
judgment of the *erased* term, which is the one the normalization proof is
about.
-/

namespace BusyLean.FT

open Ty

inductive CTm where
  | var : Nat → CTm
  | lam : Ty → CTm → CTm
  | app : CTm → CTm → CTm
  | tlam : CTm → CTm
  | tapp : CTm → Ty → CTm
  | orc : CTm
  | con : Nat → CTm

def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth? xs n

/-- Type inference in a context of term-variable types (innermost first). -/
def infer : List Ty → CTm → Option Ty
  | Γ, .var n => nth? Γ n
  | Γ, .lam A b => (infer (A :: Γ) b).map (arr A)
  | Γ, .app t u =>
      match infer Γ t, infer Γ u with
      | some (arr A B), some A' => if A = A' then some B else none
      | _, _ => none
  | Γ, .tlam b => (infer (Γ.map (tren Nat.succ)) b).map all
  | Γ, .tapp t B =>
      match infer Γ t with
      | some (all A) => some (Ty.inst A B)
      | _ => none
  | _, .orc => some (arr Ty.nat Ty.nat)
  | _, .con 0 => some Ty.tree
  | _, .con 1 => some (arr Ty.tree Ty.tree)
  | _, .con 2 => some (arr (arr Ty.nat Ty.tree) Ty.tree)
  | _, .con _ => none

/-- Type erasure. -/
def erase : CTm → Tm
  | .var n => .var n
  | .lam _ b => .lam (erase b)
  | .app t u => .app (erase t) (erase u)
  | .tlam b => erase b
  | .tapp t _ => erase t
  | .orc => .orc
  | .con k => .con k

/-- A list context as a total context (unbound variables get type `nat`). -/
def ctxOf (Γ : List Ty) : Ctx := fun n => (nth? Γ n).getD Ty.nat

theorem ctxOf_cons (A : Ty) (Γ : List Ty) : ctxOf (A :: Γ) = Ctx.cons A (ctxOf Γ) := by
  funext n; cases n <;> rfl

theorem nth?_map {α β : Type} (g : α → β) : ∀ (l : List α) (n : Nat),
    nth? (l.map g) n = (nth? l n).map g
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => nth?_map g l n

theorem ctxOf_lift (Γ : List Ty) : ctxOf (Γ.map (tren Nat.succ)) = Ctx.lift (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (tren Nat.succ)) n).getD Ty.nat = tren Nat.succ ((nth? Γ n).getD Ty.nat)
  rw [nth?_map]
  cases nth? Γ n <;> rfl

theorem infer_sound : ∀ (t : CTm) {Γ : List Ty} {A : Ty},
    infer Γ t = some A → Typed true (ctxOf Γ) (erase t) A
  | .var n, Γ, A, h => by
      have e : ctxOf Γ n = A := by
        show (nth? Γ n).getD Ty.nat = A
        rw [show nth? Γ n = some A from h]; rfl
      rw [← e]
      exact Typed.var n
  | .lam B b, Γ, A, h => by
      simp only [infer] at h
      cases hb : infer (B :: Γ) b with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          have ih := infer_sound b hb
          rw [ctxOf_cons] at ih
          exact Typed.lam ih
  | .app t u, Γ, A, h => by
      simp only [infer] at h
      cases ht : infer Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          cases hu : infer Γ u with
          | none => rw [ht, hu] at h; cases T <;> cases h
          | some U =>
              rw [ht, hu] at h
              cases T with
              | tvar _ => cases h
              | all _ => cases h
              | tree => cases h
              | arr P Q =>
                  change (if P = U then some Q else none) = some A at h
                  by_cases e : P = U
                  · rw [ite_eq_left e] at h
                    cases h
                    subst e
                    exact Typed.app (infer_sound t ht) (infer_sound u hu)
                  · rw [ite_eq_right e] at h; cases h
  | .tlam b, Γ, A, h => by
      simp only [infer] at h
      cases hb : infer (Γ.map (tren Nat.succ)) b with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          have ih := infer_sound b hb
          rw [ctxOf_lift] at ih
          exact Typed.gen ih
  | .tapp t B, Γ, A, h => by
      simp only [infer] at h
      cases ht : infer Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          cases T with
          | tvar _ => cases h
          | arr _ _ => cases h
          | tree => cases h
          | all P =>
              cases h
              exact Typed.inst B (infer_sound t ht)
  | .orc, Γ, A, h => by
      simp only [infer] at h
      cases h
      exact Typed.orc rfl
  | .con 0, Γ, A, h => by simp only [infer] at h; cases h; exact Typed.cz
  | .con 1, Γ, A, h => by simp only [infer] at h; cases h; exact Typed.cs
  | .con 2, Γ, A, h => by simp only [infer] at h; cases h; exact Typed.cl
  | .con (_ + 3), Γ, A, h => by simp only [infer] at h; cases h

end BusyLean.FT
