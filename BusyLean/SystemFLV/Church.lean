import BusyLean.SystemFLV.Typing

/-!
# Church-style ladder with universe levels, and a sound type checker

As for `SystemFLT2`, with **level abstraction** `llam l t` (`Λb ≤ l. t`) and
**level application** `lapp t c`. A level application is accepted when the
bounds force `c ≤ l` (`lle`). Type equality is decided up to `fuel` steps of
type normalization, so the check is sound (`infer_sound`) but may reject
typable programs.
-/

namespace BusyLean.FLV

open BusyLean.FL (AtomOrder)
open BusyLean.FT2 (Tm)
open BusyLean.Fw (nth?)
open Ty

variable {α : Type}

inductive CTm (α : Type) where
  | var : Nat → CTm α
  | lam : Ty α → CTm α → CTm α
  | app : CTm α → CTm α → CTm α
  | tlam : Kind α → CTm α → CTm α
  | tapp : CTm α → Ty α → CTm α
  | klam0 : CTm α → CTm α
  | kapp0 : CTm α → Kind α → CTm α
  | klam1 : CTm α → CTm α
  | kapp1 : CTm α → Kind α → CTm α
  /-- Level abstraction `Λb ≤ l. t`. -/
  | llam : Lvl α → CTm α → CTm α
  /-- Level application. -/
  | lapp : CTm α → Lvl α → CTm α
  | orc : CTm α

def erase : CTm α → Tm
  | .var n => .var n
  | .lam _ b => .lam (erase b)
  | .app t u => .app (erase t) (erase u)
  | .tlam _ b => erase b
  | .tapp t _ => erase t
  | .klam0 t => erase t
  | .kapp0 t _ => erase t
  | .klam1 t => erase t
  | .kapp1 t _ => erase t
  | .llam _ t => erase t
  | .lapp t _ => erase t
  | .orc => .orc

def ctxOf (Γ : List (Ty α)) : Ctx α := fun n => (nth? Γ n).getD Ty.nat

theorem ctxOf_cons (A : Ty α) (Γ : List (Ty α)) : ctxOf (A :: Γ) = Ctx.cons A (ctxOf Γ) := by
  funext n; cases n <;> rfl

theorem ctxOf_lift (Γ : List (Ty α)) : ctxOf (Γ.map (tren Nat.succ)) = Ctx.lift (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (tren Nat.succ)) n).getD Ty.nat = tren Nat.succ ((nth? Γ n).getD Ty.nat)
  rw [FL.nth?_map]
  cases nth? Γ n <;> rfl

theorem ctxOf_klift0 (Γ : List (Ty α)) :
    ctxOf (Γ.map (Ty.kren Nat.succ id)) = Ctx.klift0 (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (Ty.kren Nat.succ id)) n).getD Ty.nat =
    Ty.kren Nat.succ id ((nth? Γ n).getD Ty.nat)
  rw [FL.nth?_map]
  cases nth? Γ n <;> rfl

theorem ctxOf_klift1 (Γ : List (Ty α)) :
    ctxOf (Γ.map (Ty.kren id Nat.succ)) = Ctx.klift1 (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map (Ty.kren id Nat.succ)) n).getD Ty.nat =
    Ty.kren id Nat.succ ((nth? Γ n).getD Ty.nat)
  rw [FL.nth?_map]
  cases nth? Γ n <;> rfl

theorem ctxOf_llift (Γ : List (Ty α)) : ctxOf (Γ.map Ty.lsh) = Ctx.llift (ctxOf Γ) := by
  funext n
  show (nth? (Γ.map Ty.lsh) n).getD Ty.nat = ((nth? Γ n).getD Ty.nat).lsh
  rw [FL.nth?_map]
  cases nth? Γ n <;> rfl

variable [DecidableEq α] [AtomOrder α]

/-- Result type of an application, given the function and argument types. -/
def appResult (fuel : Nat) (T U : Ty α) : Option (Ty α) :=
  match tnf fuel T with
  | arr A B => if tnf fuel A = tnf fuel U then some B else none
  | _ => none

/-- Result type of a type application. -/
def tappResult (fuel : Nat) (Λ : List (Lvl α)) (Δ : List (Kind α)) (T B : Ty α) : Option (Ty α) :=
  match tnf fuel T with
  | all k A => if inferKind Λ Δ B = some k then some (Ty.inst A B) else none
  | _ => none

/-- Result type of a level-0 kind application. -/
def kappResult0 (fuel : Nat) (T : Ty α) (K : Kind α) : Option (Ty α) :=
  match tnf fuel T with
  | kall0 A => if K.dynFree = true then some (Ty.kinst0 A K) else none
  | _ => none

/-- Result type of a level-1 kind application. -/
def kappResult1 (fuel : Nat) (T : Ty α) (K : Kind α) : Option (Ty α) :=
  match tnf fuel T with
  | kall1 A => some (Ty.kinst1 A K)
  | _ => none

/-- Result type of a level application. -/
def lappResult (fuel : Nat) (Λ : List (Lvl α)) (T : Ty α) (c : Lvl α) : Option (Ty α) :=
  match tnf fuel T with
  | lall l A => if lle Λ c l = true then some (A.linst c) else none
  | _ => none

/-- Type inference with `fuel` steps of type normalization per conversion. -/
def infer (fuel : Nat) : List (Lvl α) → List (Kind α) → List (Ty α) → CTm α → Option (Ty α)
  | _, _, Γ, .var n => nth? Γ n
  | Λ, Δ, Γ, .lam A b =>
      match inferKind Λ Δ A with
      | some .star => (infer fuel Λ Δ (A :: Γ) b).map (arr A)
      | _ => none
  | Λ, Δ, Γ, .app t u =>
      match infer fuel Λ Δ Γ t, infer fuel Λ Δ Γ u with
      | some T, some U => appResult fuel T U
      | _, _ => none
  | Λ, Δ, Γ, .tlam k b => (infer fuel Λ (k :: Δ) (Γ.map (tren Nat.succ)) b).map (all k)
  | Λ, Δ, Γ, .tapp t B =>
      match infer fuel Λ Δ Γ t with
      | some T => tappResult fuel Λ Δ T B
      | none => none
  | Λ, Δ, Γ, .klam0 t =>
      (infer fuel Λ (Δ.map Kind.sh₀) (Γ.map (Ty.kren Nat.succ id)) t).map kall0
  | Λ, Δ, Γ, .kapp0 t K =>
      match infer fuel Λ Δ Γ t with
      | some T => kappResult0 fuel T K
      | none => none
  | Λ, Δ, Γ, .klam1 t =>
      (infer fuel Λ (Δ.map Kind.sh₁) (Γ.map (Ty.kren id Nat.succ)) t).map kall1
  | Λ, Δ, Γ, .kapp1 t K =>
      match infer fuel Λ Δ Γ t with
      | some T => kappResult1 fuel T K
      | none => none
  | Λ, Δ, Γ, .llam l t =>
      (infer fuel (l :: Λ) (Δ.map Kind.lsh) (Γ.map Ty.lsh) t).map (lall l)
  | Λ, Δ, Γ, .lapp t c =>
      match infer fuel Λ Δ Γ t with
      | some T => lappResult fuel Λ T c
      | none => none
  | _, _, _, .orc => some (arr Ty.nat Ty.nat)

/-- All types in the context have kind `★`. -/
def GoodCtx (Λ : List (Lvl α)) (Δ : List (Kind α)) (Γ : List (Ty α)) : Prop :=
  ∀ n A, nth? Γ n = some A → Kinded Λ (kctxOf Δ) A .star

theorem GoodCtx.cons {Λ : List (Lvl α)} {Δ : List (Kind α)} {Γ : List (Ty α)}
    (h : GoodCtx Λ Δ Γ) {A : Ty α} (hA : Kinded Λ (kctxOf Δ) A .star) :
    GoodCtx Λ Δ (A :: Γ) := fun n B hB => by
  cases n with
  | zero => cases hB; exact hA
  | succ n => exact h n B hB

theorem GoodCtx.lift {Λ : List (Lvl α)} {Δ : List (Kind α)} {Γ : List (Ty α)}
    (h : GoodCtx Λ Δ Γ) (k : Kind α) : GoodCtx Λ (k :: Δ) (Γ.map (tren Nat.succ)) :=
  fun n B hB => by
    rw [FL.nth?_map] at hB
    cases hn : nth? Γ n with
    | none => rw [hn] at hB; cases hB
    | some A =>
        rw [hn] at hB
        cases hB
        rw [kctxOf_cons]
        exact (h n A hn).ren fun _ => rfl

theorem GoodCtx.klift0 {Λ : List (Lvl α)} {Δ : List (Kind α)} {Γ : List (Ty α)}
    (h : GoodCtx Λ Δ Γ) : GoodCtx Λ (Δ.map Kind.sh₀) (Γ.map (Ty.kren Nat.succ id)) :=
  fun n B hB => by
    rw [FL.nth?_map] at hB
    cases hn : nth? Γ n with
    | none => rw [hn] at hB; cases hB
    | some A =>
        rw [hn] at hB
        cases hB
        rw [kctxOf_klift0]
        exact (h n A hn).kren Nat.succ id

theorem GoodCtx.klift1 {Λ : List (Lvl α)} {Δ : List (Kind α)} {Γ : List (Ty α)}
    (h : GoodCtx Λ Δ Γ) : GoodCtx Λ (Δ.map Kind.sh₁) (Γ.map (Ty.kren id Nat.succ)) :=
  fun n B hB => by
    rw [FL.nth?_map] at hB
    cases hn : nth? Γ n with
    | none => rw [hn] at hB; cases hB
    | some A =>
        rw [hn] at hB
        cases hB
        rw [kctxOf_klift1]
        exact (h n A hn).kren id Nat.succ

theorem GoodCtx.llift {Λ : List (Lvl α)} {Δ : List (Kind α)} {Γ : List (Ty α)}
    (h : GoodCtx Λ Δ Γ) (l : Lvl α) : GoodCtx (l :: Λ) (Δ.map Kind.lsh) (Γ.map Ty.lsh) :=
  fun n B hB => by
    rw [FL.nth?_map] at hB
    cases hn : nth? Γ n with
    | none => rw [hn] at hB; cases hB
    | some A =>
        rw [hn] at hB
        cases hB
        rw [kctxOf_llift]
        exact (h n A hn).lsubst (LMap.weaken l Λ)

theorem ctxOf_kinded {Λ : List (Lvl α)} {Δ : List (Kind α)} {Γ : List (Ty α)}
    (h : GoodCtx Λ Δ Γ) (n : Nat) : Kinded Λ (kctxOf Δ) (ctxOf Γ n) .star := by
  show Kinded _ _ ((nth? Γ n).getD Ty.nat) _
  cases hn : nth? Γ n with
  | none => exact Kinded.nat _ _
  | some A => exact h n A hn

omit [AtomOrder α] in
theorem appResult_inv {fuel : Nat} {T U A : Ty α} (h : appResult fuel T U = some A) :
    ∃ P, TSteps T (arr P A) ∧ TJoin P U := by
  unfold appResult at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  split at h
  · next P Q =>
      split at h
      · next e => cases h; exact ⟨P, sT, tjoin_of_tnf e⟩
      · cases h
  · cases h

theorem tappResult_inv {fuel : Nat} {Λ : List (Lvl α)} {Δ : List (Kind α)} {T B A : Ty α}
    (h : tappResult fuel Λ Δ T B = some A) :
    ∃ k P, TSteps T (all k P) ∧ inferKind Λ Δ B = some k ∧ A = Ty.inst P B := by
  unfold tappResult at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  split at h
  · next k P =>
      split at h
      · next e => cases h; exact ⟨k, P, sT, e, rfl⟩
      · cases h
  · cases h

omit [AtomOrder α] in
theorem kappResult0_inv {fuel : Nat} {T A : Ty α} {K : Kind α}
    (h : kappResult0 fuel T K = some A) :
    ∃ P, TSteps T (kall0 P) ∧ K.DynFree ∧ A = Ty.kinst0 P K := by
  unfold kappResult0 at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  split at h
  · next P =>
      split at h
      · next e => cases h; exact ⟨P, sT, (Kind.dynFree_iff K).1 e, rfl⟩
      · cases h
  · cases h

omit [AtomOrder α] in
theorem kappResult1_inv {fuel : Nat} {T A : Ty α} {K : Kind α}
    (h : kappResult1 fuel T K = some A) :
    ∃ P, TSteps T (kall1 P) ∧ A = Ty.kinst1 P K := by
  unfold kappResult1 at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  split at h
  · next P => cases h; exact ⟨P, sT, rfl⟩
  · cases h

theorem lappResult_inv {fuel : Nat} {Λ : List (Lvl α)} {T A : Ty α} {c : Lvl α}
    (h : lappResult fuel Λ T c = some A) :
    ∃ l P, TSteps T (lall l P) ∧ lle Λ c l = true ∧ A = P.linst c := by
  unfold lappResult at h
  have sT := tnf_steps fuel T
  revert h
  generalize tnf fuel T = N at sT
  intro h
  split at h
  · next l P =>
      split at h
      · next e => cases h; exact ⟨l, P, sT, e, rfl⟩
      · cases h
  · cases h

/-- **Soundness of type checking**: accepted programs are typable, at a kinded type. -/
theorem infer_sound (htr : LtTrans α) (fuel : Nat) : ∀ (t : CTm α) {Λ : List (Lvl α)}
    {Δ : List (Kind α)} {Γ : List (Ty α)} {A : Ty α},
    GoodCtx Λ Δ Γ → infer fuel Λ Δ Γ t = some A →
      Typed true Λ (kctxOf Δ) (ctxOf Γ) (erase t) A ∧ Kinded Λ (kctxOf Δ) A .star
  | .var n, Λ, Δ, Γ, A, hΓ, h => by
      have e : ctxOf Γ n = A := by
        show (nth? Γ n).getD Ty.nat = A
        rw [show nth? Γ n = some A from h]; rfl
      refine ⟨?_, hΓ n A h⟩
      rw [← e]
      exact Typed.var n
  | .lam B b, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hk : inferKind Λ Δ B with
      | none => rw [hk] at h; cases h
      | some k =>
          rw [hk] at h
          cases k with
          | star =>
              have hB := inferKind_sound B hk
              cases hb : infer fuel Λ Δ (B :: Γ) b with
              | none => rw [hb] at h; cases h
              | some C =>
                  rw [hb] at h
                  cases h
                  obtain ⟨ih, hC⟩ := infer_sound htr fuel b (hΓ.cons hB) hb
                  rw [ctxOf_cons] at ih
                  exact ⟨Typed.lam ih, Kinded.arr hB hC⟩
          | _ => cases h
  | .app t u, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Λ Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          cases hu : infer fuel Λ Δ Γ u with
          | none => rw [ht, hu] at h; cases h
          | some U =>
              rw [ht, hu] at h
              obtain ⟨tyT, kT⟩ := infer_sound htr fuel t hΓ ht
              obtain ⟨tyU, kU⟩ := infer_sound htr fuel u hΓ hu
              obtain ⟨P, sT, j⟩ := appResult_inv h
              have kPA := kT.steps htr sT
              cases kPA with
              | arr kP kA =>
                  have t' := Typed.conv tyT kT (Kinded.arr kP kA) sT.join_left
                  have u' := Typed.conv tyU kU kP j.symm
                  exact ⟨Typed.app t' u', kA⟩
  | .tlam k b, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hb : infer fuel Λ (k :: Δ) (Γ.map (tren Nat.succ)) b with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          obtain ⟨ih, hC⟩ := infer_sound htr fuel b (hΓ.lift k) hb
          rw [kctxOf_cons, ctxOf_lift] at ih
          rw [kctxOf_cons] at hC
          exact ⟨Typed.gen ih, Kinded.all hC⟩
  | .tapp t B, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Λ Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          obtain ⟨tyT, kT⟩ := infer_sound htr fuel t hΓ ht
          obtain ⟨k, P, sT, e, rfl⟩ := tappResult_inv h
          have kAll := kT.steps htr sT
          cases kAll with
          | all kP =>
              have hB := inferKind_sound B e
              have t' := Typed.conv tyT kT (Kinded.all kP) sT.join_left
              exact ⟨Typed.inst B t' kP hB, kP.inst hB⟩
  | .klam0 t, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hb : infer fuel Λ (Δ.map Kind.sh₀) (Γ.map (Ty.kren Nat.succ id)) t with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          obtain ⟨ih, hC⟩ := infer_sound htr fuel t hΓ.klift0 hb
          rw [kctxOf_klift0, ctxOf_klift0] at ih
          rw [kctxOf_klift0] at hC
          exact ⟨Typed.kgen0 ih, Kinded.kall0 hC⟩
  | .kapp0 t K, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Λ Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          obtain ⟨tyT, kT⟩ := infer_sound htr fuel t hΓ ht
          obtain ⟨P, sT, hK, rfl⟩ := kappResult0_inv h
          have kAll := kT.steps htr sT
          cases kAll with
          | kall0 kP =>
              have t' := Typed.conv tyT kT (Kinded.kall0 kP) sT.join_left
              exact ⟨Typed.kinst0 K t' hK, kP.kinst0 hK⟩
  | .klam1 t, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hb : infer fuel Λ (Δ.map Kind.sh₁) (Γ.map (Ty.kren id Nat.succ)) t with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          obtain ⟨ih, hC⟩ := infer_sound htr fuel t hΓ.klift1 hb
          rw [kctxOf_klift1, ctxOf_klift1] at ih
          rw [kctxOf_klift1] at hC
          exact ⟨Typed.kgen1 ih, Kinded.kall1 hC⟩
  | .kapp1 t K, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Λ Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          obtain ⟨tyT, kT⟩ := infer_sound htr fuel t hΓ ht
          obtain ⟨P, sT, rfl⟩ := kappResult1_inv h
          have kAll := kT.steps htr sT
          cases kAll with
          | kall1 kP =>
              have t' := Typed.conv tyT kT (Kinded.kall1 kP) sT.join_left
              exact ⟨Typed.kinst1 K t', kP.kinst1 K⟩
  | .llam l t, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases hb : infer fuel (l :: Λ) (Δ.map Kind.lsh) (Γ.map Ty.lsh) t with
      | none => rw [hb] at h; cases h
      | some C =>
          rw [hb] at h
          cases h
          obtain ⟨ih, hC⟩ := infer_sound htr fuel t (hΓ.llift l) hb
          rw [kctxOf_llift, ctxOf_llift] at ih
          rw [kctxOf_llift] at hC
          exact ⟨Typed.lgen ih, Kinded.lall hC⟩
  | .lapp t c, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases ht : infer fuel Λ Δ Γ t with
      | none => rw [ht] at h; cases h
      | some T =>
          rw [ht] at h
          obtain ⟨tyT, kT⟩ := infer_sound htr fuel t hΓ ht
          obtain ⟨l, P, sT, hc, rfl⟩ := lappResult_inv h
          have kAll := kT.steps htr sT
          cases kAll with
          | lall kP =>
              have t' := Typed.conv tyT kT (Kinded.lall kP) sT.join_left
              exact ⟨Typed.linst c t' hc, Kinded.linst htr kP hc⟩
  | .orc, Λ, Δ, Γ, A, hΓ, h => by
      simp only [infer] at h
      cases h
      exact ⟨Typed.orc rfl, Kinded.arr (Kinded.nat _ _) (Kinded.nat _ _)⟩

theorem goodCtx_nil (Λ : List (Lvl α)) (Δ : List (Kind α)) : GoodCtx Λ Δ [] :=
  fun _ _ h => nomatch h

end BusyLean.FLV
