import BusyLean.Independent.SystemTLtLadder

/-!
# A verified type checker for the System F fragment (proof infrastructure)

Programs of the ladder language that use only System F (type variables,
arrows, `∀` over `★`, no atoms) are written here in their own atom-free
syntax `FTm`, with types `FTy`. `checkF` is a fuel-free type checker for it,
comparing types syntactically. It is **sound** for the ladder's type checker:
if `checkF 0 [] t = some T`, then the ladder accepts the embedded program at
every fuel and in every context, with the embedded type (`checkF_sound`).

So the typing of a concrete program is a computation, checked by the kernel.
The embedded programs lie in the System F fragment (`isFC_embC`), erase to
`eraseF`, and have depth `cdepthF`.
-/

namespace BusyLean.Indep.SF

open BusyLean.FL
open BusyLean.Fw (nth?)
open BusyLean.F.Tm (upRen)

/-- System F types without atoms: `∀` binds a type variable of kind `★`. -/
inductive FTy where
  | tvar : Nat → FTy
  | arr : FTy → FTy → FTy
  | all : FTy → FTy
  deriving DecidableEq

/-- Church-style System F terms without atoms. -/
inductive FTm where
  | var : Nat → FTm
  | lam : FTy → FTm → FTm
  | app : FTm → FTm → FTm
  | tlam : FTm → FTm
  | tapp : FTm → FTy → FTm

namespace FTy

def ren (ξ : Nat → Nat) : FTy → FTy
  | tvar n => tvar (ξ n)
  | arr A B => arr (ren ξ A) (ren ξ B)
  | all A => all (ren (upRen ξ) A)

def up (σ : Nat → FTy) : Nat → FTy
  | 0 => tvar 0
  | n + 1 => ren Nat.succ (σ n)

def subst (σ : Nat → FTy) : FTy → FTy
  | tvar n => σ n
  | arr A B => arr (subst σ A) (subst σ B)
  | all A => all (subst (up σ) A)

def cons (B : FTy) (σ : Nat → FTy) : Nat → FTy
  | 0 => B
  | n + 1 => σ n

def inst (A B : FTy) : FTy := subst (cons B tvar) A

/-- All free type variables are `< k`. -/
def wf : Nat → FTy → Bool
  | k, tvar n => decide (n < k)
  | k, arr A B => wf k A && wf k B
  | k, all A => wf (k + 1) A

end FTy

open FTy

/-- The type checker. `k` counts the enclosing type binders. -/
def checkF : Nat → List FTy → FTm → Option FTy
  | _, Γ, .var n => nth? Γ n
  | k, Γ, .lam A b => if A.wf k then (checkF k (A :: Γ) b).map (FTy.arr A) else none
  | k, Γ, .app t u =>
      match checkF k Γ t, checkF k Γ u with
      | some (.arr A B), some U => if A = U then some B else none
      | _, _ => none
  | k, Γ, .tlam b => (checkF (k + 1) (Γ.map (FTy.ren Nat.succ)) b).map FTy.all
  | k, Γ, .tapp t B =>
      match checkF k Γ t with
      | some (.all A) => if B.wf k then some (FTy.inst A B) else none
      | _ => none

/-! ## Embedding into the ladder language -/

variable {α : Type}

def embT : FTy → FL.Ty α
  | .tvar n => .tvar n
  | .arr A B => .arr (embT A) (embT B)
  | .all A => .all .star (embT A)

def embC : FTm → CTm α
  | .var n => .var n
  | .lam A b => .lam (embT A) (embC b)
  | .app t u => .app (embC t) (embC u)
  | .tlam b => .tlam .star (embC b)
  | .tapp t A => .tapp (embC t) (embT A)

/-- The erasure of an `FTm`. -/
def eraseF : FTm → F.Tm
  | .var n => .var n
  | .lam _ b => .lam (eraseF b)
  | .app t u => .app (eraseF t) (eraseF u)
  | .tlam b => eraseF b
  | .tapp t _ => eraseF t

def tdepthF : FTy → Nat
  | .tvar n => n + 2
  | .arr A B => max (tdepthF A) (tdepthF B) + 1
  | .all A => tdepthF A + 1

def cdepthF : FTm → Nat
  | .var n => n + 2
  | .lam A e => max (tdepthF A) (cdepthF e) + 1
  | .app t u => max (cdepthF t) (cdepthF u) + 1
  | .tlam e => cdepthF e + 1
  | .tapp e A => max (cdepthF e) (tdepthF A) + 1

theorem erase_embC [DecidableEq α] [AtomOrder α] :
    ∀ t : FTm, FL.erase (embC t : CTm α) = eraseF t
  | .var _ => rfl
  | .lam _ b => congrArg F.Tm.lam (erase_embC b)
  | .app t u => by
      show F.Tm.app (FL.erase (embC t : CTm α)) (FL.erase (embC u : CTm α)) = _
      rw [erase_embC t, erase_embC u]; rfl
  | .tlam b => erase_embC b
  | .tapp t _ => erase_embC t

theorem tdepth_embT : ∀ A : FTy, Emb.tdepth (embT A : FL.Ty α) = tdepthF A
  | .tvar _ => rfl
  | .arr A B => by
      show max (Emb.tdepth (embT A : FL.Ty α)) (Emb.tdepth (embT B : FL.Ty α)) + 1 = _
      rw [tdepth_embT A, tdepth_embT B]; rfl
  | .all A => by
      show Emb.tdepth (embT A : FL.Ty α) + 1 = _
      rw [tdepth_embT A]; rfl

theorem cdepth_embC : ∀ t : FTm, Emb.cdepth (embC t : CTm α) = cdepthF t
  | .var _ => rfl
  | .lam A b => by
      show max (Emb.tdepth (embT A : FL.Ty α)) (Emb.cdepth (embC b : CTm α)) + 1 = _
      rw [tdepth_embT A, cdepth_embC b]; rfl
  | .app t u => by
      show max (Emb.cdepth (embC t : CTm α)) (Emb.cdepth (embC u : CTm α)) + 1 = _
      rw [cdepth_embC t, cdepth_embC u]; rfl
  | .tlam b => by
      show Emb.cdepth (embC b : CTm α) + 1 = _
      rw [cdepth_embC b]; rfl
  | .tapp t A => by
      show max (Emb.cdepth (embC t : CTm α)) (Emb.tdepth (embT A : FL.Ty α)) + 1 = _
      rw [cdepth_embC t, tdepth_embT A]; rfl

theorem isF_embT : ∀ A : FTy, Emb.IsF (embT A : FL.Ty α)
  | .tvar _ => trivial
  | .arr A B => ⟨isF_embT A, isF_embT B⟩
  | .all A => ⟨rfl, isF_embT A⟩

theorem isFC_embC : ∀ t : FTm, Emb.IsFC (embC t : CTm α)
  | .var _ => trivial
  | .lam A b => ⟨isF_embT A, isFC_embC b⟩
  | .app t u => ⟨isFC_embC t, isFC_embC u⟩
  | .tlam b => ⟨rfl, isFC_embC b⟩
  | .tapp t A => ⟨isFC_embC t, isF_embT A⟩

/-! ## Types: renaming, substitution, normal forms, kinds -/

theorem embT_ren : ∀ (A : FTy) (ξ : Nat → Nat), embT (A.ren ξ) = Ty.tren ξ (embT A : FL.Ty α)
  | .tvar _, _ => rfl
  | .arr A B, ξ => by
      show FL.Ty.arr (embT (A.ren ξ)) (embT (B.ren ξ)) = _
      rw [embT_ren A ξ, embT_ren B ξ]; rfl
  | .all A, ξ => by
      show FL.Ty.all .star (embT (A.ren (upRen ξ))) = _
      rw [embT_ren A (upRen ξ)]; rfl

theorem embT_up (σ : Nat → FTy) :
    (fun n => (embT (FTy.up σ n) : FL.Ty α)) = Ty.tup (fun n => embT (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact embT_ren (σ n) Nat.succ

theorem embT_subst : ∀ (A : FTy) (σ : Nat → FTy),
    embT (A.subst σ) = Ty.tsubst (fun n => embT (σ n)) (embT A : FL.Ty α)
  | .tvar _, _ => rfl
  | .arr A B, σ => by
      show FL.Ty.arr (embT (A.subst σ)) (embT (B.subst σ)) = _
      rw [embT_subst A σ, embT_subst B σ]; rfl
  | .all A, σ => by
      show FL.Ty.all .star (embT (A.subst (FTy.up σ))) = _
      rw [embT_subst A (FTy.up σ), embT_up σ]; rfl

theorem embT_inst (A B : FTy) : embT (A.inst B) = Ty.inst (embT A : FL.Ty α) (embT B) := by
  show embT (A.subst (FTy.cons B FTy.tvar)) = _
  rw [embT_subst]
  show Ty.tsubst (fun n => embT (FTy.cons B FTy.tvar n)) (embT A) =
    Ty.tsubst (Ty.tcons (embT B) Ty.tvar) (embT A)
  congr 1
  funext n
  cases n <;> rfl

variable [DecidableEq α] [AtomOrder α]

theorem tstep_embT : ∀ A : FTy, tstep (embT A : FL.Ty α) = none
  | .tvar _ => rfl
  | .arr A B => by
      show (match tstep (embT A : FL.Ty α) with
        | some A' => some (FL.Ty.arr A' (embT B))
        | none => (tstep (embT B : FL.Ty α)).map (FL.Ty.arr (embT A))) = none
      rw [tstep_embT A, tstep_embT B]; rfl
  | .all A => by
      show (tstep (embT A : FL.Ty α)).map (FL.Ty.all .star) = none
      rw [tstep_embT A]; rfl

theorem kind_embT : ∀ (A : FTy) {k : Nat} {Δ : List (Kind α)}, A.wf k = true →
    (∀ i, i < k → nth? Δ i = some .star) → inferKind Δ (embT A) = some .star
  | .tvar n, k, Δ, h, hΔ => hΔ n (of_decide_eq_true h)
  | .arr A B, k, Δ, h, hΔ => by
      have hAB : A.wf k = true ∧ B.wf k = true := by
        simp only [FTy.wf, Bool.and_eq_true] at h; exact h
      show arrK (inferKind Δ (embT A)) (inferKind Δ (embT B)) = _
      rw [kind_embT A hAB.1 hΔ, kind_embT B hAB.2 hΔ]; rfl
  | .all A, k, Δ, h, hΔ => by
      show starK (inferKind (.star :: Δ) (embT A)) = _
      have hΔ' : ∀ i, i < k + 1 → nth? (Kind.star :: Δ) i = some .star := fun i hi => by
        cases i with
        | zero => rfl
        | succ i => exact hΔ i (Nat.lt_of_succ_lt_succ hi)
      rw [kind_embT A h hΔ']; rfl

/-! ## Soundness -/

theorem nth?_append_left {β : Type} {G : List β} :
    ∀ {Γ : List β} {n : Nat} {x : β}, nth? Γ n = some x → nth? (Γ ++ G) n = some x
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, h => h
  | _ :: Γ, n + 1, _, h => nth?_append_left (Γ := Γ) (n := n) h

theorem nth?_map_some {β γ : Type} (g : β → γ) :
    ∀ {Γ : List β} {n : Nat} {x : β}, nth? Γ n = some x → nth? (Γ.map g) n = some (g x)
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, h => by cases h; rfl
  | _ :: Γ, n + 1, _, h => nth?_map_some g (Γ := Γ) (n := n) h

omit [DecidableEq α] [AtomOrder α] in
theorem map_ren_embT (Γ : List FTy) (G : List (FL.Ty α)) :
    (Γ.map embT ++ G).map (Ty.tren Nat.succ) =
      (Γ.map (FTy.ren Nat.succ)).map embT ++ G.map (Ty.tren Nat.succ) := by
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro A _
  exact (embT_ren A Nat.succ).symm

/-- **Soundness of `checkF`.** -/
theorem checkF_sound : ∀ (t : FTm) {k : Nat} {Γ : List FTy} {T : FTy}, checkF k Γ t = some T →
    ∀ {fuel : Nat} {Δ : List (Kind α)}, (∀ i, i < k → nth? Δ i = some .star) →
    ∀ (G : List (FL.Ty α)), infer fuel Δ (Γ.map embT ++ G) (embC t) = some (embT T)
  | .var n, k, Γ, T, h, fuel, Δ, _, G => by
      show nth? (Γ.map embT ++ G) n = _
      exact nth?_append_left (nth?_map_some embT h)
  | .lam A b, k, Γ, T, h, fuel, Δ, hΔ, G => by
      simp only [checkF] at h
      split at h
      · next hA =>
          cases hb : checkF k (A :: Γ) b with
          | none => rw [hb] at h; cases h
          | some B =>
              rw [hb] at h
              cases h
              exact Emb.infer_lam (kind_embT A hA hΔ) (checkF_sound b hb hΔ G)
      · cases h
  | .app t u, k, Γ, T, h, fuel, Δ, hΔ, G => by
      cases ht : checkF k Γ t with
      | none => simp only [checkF, ht] at h; cases h
      | some Tt =>
          cases hu : checkF k Γ u with
          | none => simp only [checkF, ht, hu] at h; cases h
          | some U =>
              cases Tt with
              | arr A B =>
                  simp only [checkF, ht, hu] at h
                  by_cases hAU : A = U
                  · subst hAU
                    simp only [↓reduceIte, Option.some.injEq] at h
                    subst h
                    exact Emb.infer_app (checkF_sound t ht hΔ G) (checkF_sound u hu hΔ G)
                      (tstep_embT (.arr A B))
                  · simp only [hAU, ↓reduceIte] at h
                    cases h
              | tvar _ => simp only [checkF, ht, hu] at h; cases h
              | all _ => simp only [checkF, ht, hu] at h; cases h
  | .tlam b, k, Γ, T, h, fuel, Δ, hΔ, G => by
      simp only [checkF] at h
      cases hb : checkF (k + 1) (Γ.map (FTy.ren Nat.succ)) b with
      | none => rw [hb] at h; cases h
      | some B =>
          rw [hb] at h
          cases h
          have hΔ' : ∀ i, i < k + 1 → nth? (Kind.star :: Δ) i = some .star := fun i hi => by
            cases i with
            | zero => rfl
            | succ i => exact hΔ i (Nat.lt_of_succ_lt_succ hi)
          have ih := checkF_sound b hb (fuel := fuel) hΔ' (G.map (Ty.tren Nat.succ))
          rw [← map_ren_embT] at ih
          exact Emb.infer_tlam ih
  | .tapp t B, k, Γ, T, h, fuel, Δ, hΔ, G => by
      cases ht : checkF k Γ t with
      | none => simp only [checkF, ht] at h; cases h
      | some Tt =>
          cases Tt with
          | all A =>
              simp only [checkF, ht] at h
              cases hB : B.wf k with
              | false => rw [hB] at h; cases h
              | true =>
                  simp only [hB, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  rw [embT_inst]
                  exact Emb.infer_tapp (checkF_sound t ht hΔ G) (tstep_embT (.all A))
                    (kind_embT B hB hΔ)
          | tvar _ => simp only [checkF, ht] at h; cases h
          | arr _ _ => simp only [checkF, ht] at h; cases h

/-- A closed program accepted by `checkF` is accepted by the ladder everywhere. -/
theorem infer_embC {t : FTm} {T : FTy} (h : checkF 0 [] t = some T) (fuel : Nat)
    (Δ : List (Kind α)) (Γ : List (FL.Ty α)) : infer fuel Δ Γ (embC t) = some (embT T) :=
  checkF_sound t h (fun _ hi => absurd hi (Nat.not_lt_zero _)) Γ

end BusyLean.Indep.SF
