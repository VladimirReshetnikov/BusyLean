import BusyLean.Independent.FwCheck
import BusyLean.Independent.Ladder
import BusyLean.SystemFT2.FromF

/-!
# The Fω fragment inside the ladder with universe levels

`FwCheck.lean` embeds the Fω fragment (`FK`, `FTy`, `FTm`) into the ladder
language and proves its small checker `checkW` sound for the ladder's checker.
This file does the same for the ladder with universe levels (`SystemFLV`),
the language of rung 4's readers:

* the embedded kinds, types and programs have no levels, and `SystemFLV`'s
  type-level reduction agrees with `FTy.tstep` on them (`tstep_embTV`);
* so an `FTm` that `checkW F₀` accepts is accepted by `FLV.infer` at every
  fuel `≥ F₀`, in every level context and every extension of its contexts
  (`checkW_soundV`);
* embedded programs of small depth are enumerated by rung 4
  (`mem_vctmsUpTo`);
* an embedded program erases to the inclusion of its System F erasure into
  System FT2's terms (`erase_embCV`).
-/

namespace BusyLean.Indep.FW

open BusyLean.Fw (nth?)
open BusyLean.F.Tm (upRen)
open BusyLean.Indep.Ladder (vkindsUpTo vtysUpTo vctmsUpTo cross natsUpTo)
open BusyLean.Indep.Emb (mem_cross)

variable {α : Type}

def embKV : FK → FLV.Kind α
  | .star => .star
  | .arr a b => .arr (embKV a) (embKV b)

def embTV : FTy → FLV.Ty α
  | .tvar n => .tvar n
  | .arr A B => .arr (embTV A) (embTV B)
  | .all k A => .all (embKV k) (embTV A)
  | .lam k A => .lam (embKV k) (embTV A)
  | .app k A B => .app (embKV k) (embTV A) (embTV B)

def embCV : FTm → FLV.CTm α
  | .var n => .var n
  | .lam A b => .lam (embTV A) (embCV b)
  | .app t u => .app (embCV t) (embCV u)
  | .tlam k b => .tlam (embKV k) (embCV b)
  | .tapp t A => .tapp (embCV t) (embTV A)

theorem erase_embCV : ∀ t : FTm, FLV.erase (embCV t : FLV.CTm α) = FT2.embF (eraseF t)
  | .var _ => rfl
  | .lam _ b => congrArg FT2.Tm.lam (erase_embCV b)
  | .app t u => by
      show FT2.Tm.app (FLV.erase (embCV t : FLV.CTm α)) (FLV.erase (embCV u : FLV.CTm α)) = _
      rw [erase_embCV t, erase_embCV u]
      rfl
  | .tlam _ b => erase_embCV b
  | .tapp t _ => erase_embCV t

/-! ## Enumeration -/

theorem mem_vkindsUpTo (as : List α) : ∀ (k : FK) {m : Nat}, kdepthF k ≤ m →
    (embKV k : FLV.Kind α) ∈ vkindsUpTo as m
  | .star, m + 1, _ => List.mem_cons_self
  | .arr a b, m + 1, h => by
      simp only [kdepthF] at h
      refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun p : FLV.Kind α × FLV.Kind α => FLV.Kind.arr p.1 p.2)
          (mem_cross ?_ ?_))))
      · exact mem_vkindsUpTo as a (by omega)
      · exact mem_vkindsUpTo as b (by omega)
  | .star, 0, h => absurd h (by decide)
  | .arr _ _, 0, h => absurd h (Nat.not_succ_le_zero _)

theorem mem_vtysUpTo (as : List α) : ∀ (A : FTy) {m : Nat}, tdepthF A ≤ m →
    (embTV A : FLV.Ty α) ∈ vtysUpTo as m
  | .tvar n, m + 1, h =>
      List.mem_append_left _ (List.mem_map_of_mem (f := FLV.Ty.tvar)
        (Emb.mem_natsUpTo (show n < m by simp only [tdepthF] at h; omega)))
  | .arr A B, m + 1, h => by
      simp only [tdepthF] at h
      refine List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem
        (f := fun p : FLV.Ty α × FLV.Ty α => FLV.Ty.arr p.1 p.2) (mem_cross ?_ ?_)))
      · exact mem_vtysUpTo as A (by omega)
      · exact mem_vtysUpTo as B (by omega)
  | .all k A, m + 1, h => by
      simp only [tdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun p : FLV.Kind α × FLV.Ty α => FLV.Ty.all p.1 p.2)
          (mem_cross (mem_vkindsUpTo as k (by omega)) (mem_vtysUpTo as A (by omega))))))
  | .lam k A, m + 1, h => by
      simp only [tdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _
          (List.mem_map_of_mem (f := fun p : FLV.Kind α × FLV.Ty α => FLV.Ty.lam p.1 p.2)
            (mem_cross (mem_vkindsUpTo as k (by omega)) (mem_vtysUpTo as A (by omega)))))))
  | .app k A B, m + 1, h => by
      simp only [tdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _
          (List.mem_map_of_mem
            (f := fun p : FLV.Kind α × (FLV.Ty α × FLV.Ty α) => FLV.Ty.app p.1 p.2.1 p.2.2)
            (mem_cross (mem_vkindsUpTo as k (by omega))
              (mem_cross (mem_vtysUpTo as A (by omega)) (mem_vtysUpTo as B (by omega)))))))))
  | .tvar _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .arr _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .all _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .lam _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .app _ _ _, 0, h => absurd h (Nat.not_succ_le_zero _)

theorem mem_vctmsUpTo (as : List α) : ∀ (e : FTm) {m : Nat}, cdepthF e ≤ m →
    (embCV e : FLV.CTm α) ∈ vctmsUpTo as m
  | .var n, m + 1, h =>
      List.mem_append_left _ (List.mem_map_of_mem (f := FLV.CTm.var)
        (Emb.mem_natsUpTo (show n < m by simp only [cdepthF] at h; omega)))
  | .lam A e, m + 1, h => by
      simp only [cdepthF] at h
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem
        (f := fun p : FLV.Ty α × FLV.CTm α => FLV.CTm.lam p.1 p.2)
        (mem_cross (mem_vtysUpTo as A (by omega)) (mem_vctmsUpTo as e (by omega)))))
  | .app t u, m + 1, h => by
      simp only [cdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun p : FLV.CTm α × FLV.CTm α => FLV.CTm.app p.1 p.2)
        (mem_cross (mem_vctmsUpTo as t (by omega)) (mem_vctmsUpTo as u (by omega))))))
  | .tlam k e, m + 1, h => by
      simp only [cdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _
          (List.mem_map_of_mem (f := fun p : FLV.Kind α × FLV.CTm α => FLV.CTm.tlam p.1 p.2)
            (mem_cross (mem_vkindsUpTo as k (by omega)) (mem_vctmsUpTo as e (by omega)))))))
  | .tapp e A, m + 1, h => by
      simp only [cdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _
          (List.mem_map_of_mem (f := fun p : FLV.CTm α × FLV.Ty α => FLV.CTm.tapp p.1 p.2)
            (mem_cross (mem_vctmsUpTo as e (by omega)) (mem_vtysUpTo as A (by omega))))))))
  | .var _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .lam _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .app _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .tlam _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .tapp _ _, 0, h => absurd h (Nat.not_succ_le_zero _)

/-! ## Commutation with the embedding -/

theorem embTV_ren : ∀ (A : FTy) (ξ : Nat → Nat),
    embTV (A.ren ξ) = FLV.Ty.tren ξ (embTV A : FLV.Ty α)
  | .tvar _, _ => rfl
  | .arr A B, ξ => by
      show FLV.Ty.arr (embTV (A.ren ξ)) (embTV (B.ren ξ)) = _
      rw [embTV_ren A ξ, embTV_ren B ξ]; rfl
  | .all k A, ξ => by
      show FLV.Ty.all (embKV k) (embTV (A.ren (upRen ξ))) = _
      rw [embTV_ren A (upRen ξ)]; rfl
  | .lam k A, ξ => by
      show FLV.Ty.lam (embKV k) (embTV (A.ren (upRen ξ))) = _
      rw [embTV_ren A (upRen ξ)]; rfl
  | .app k A B, ξ => by
      show FLV.Ty.app (embKV k) (embTV (A.ren ξ)) (embTV (B.ren ξ)) = _
      rw [embTV_ren A ξ, embTV_ren B ξ]; rfl

theorem embTV_up (σ : Nat → FTy) :
    (fun n => (embTV (FTy.up σ n) : FLV.Ty α)) = FLV.Ty.tup (fun n => embTV (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact embTV_ren (σ n) Nat.succ

theorem embTV_subst : ∀ (A : FTy) (σ : Nat → FTy),
    embTV (A.subst σ) = FLV.Ty.tsubst (fun n => embTV (σ n)) (embTV A : FLV.Ty α)
  | .tvar _, _ => rfl
  | .arr A B, σ => by
      show FLV.Ty.arr (embTV (A.subst σ)) (embTV (B.subst σ)) = _
      rw [embTV_subst A σ, embTV_subst B σ]; rfl
  | .all k A, σ => by
      show FLV.Ty.all (embKV k) (embTV (A.subst (FTy.up σ))) = _
      rw [embTV_subst A (FTy.up σ), embTV_up σ]; rfl
  | .lam k A, σ => by
      show FLV.Ty.lam (embKV k) (embTV (A.subst (FTy.up σ))) = _
      rw [embTV_subst A (FTy.up σ), embTV_up σ]; rfl
  | .app k A B, σ => by
      show FLV.Ty.app (embKV k) (embTV (A.subst σ)) (embTV (B.subst σ)) = _
      rw [embTV_subst A σ, embTV_subst B σ]; rfl

theorem embTV_inst (A B : FTy) :
    embTV (A.inst B) = FLV.Ty.inst (embTV A : FLV.Ty α) (embTV B) := by
  show embTV (A.subst (FTy.cons B FTy.tvar)) = _
  rw [embTV_subst]
  show FLV.Ty.tsubst (fun n => embTV (FTy.cons B FTy.tvar n)) (embTV A) =
    FLV.Ty.tsubst (FLV.Ty.tcons (embTV B) FLV.Ty.tvar) (embTV A)
  congr 1
  funext n
  cases n <;> rfl

variable [DecidableEq α] [FL.AtomOrder α]

omit [DecidableEq α] [FL.AtomOrder α] in
theorem tappStep_embTV (k : FK) (A B : FTy) (sA sB : Option FTy)
    (hA : ∀ k' A₀, A ≠ FTy.lam k' A₀) :
    FLV.tappStep (embKV k) (embTV A) (embTV B) (sA.map embTV) (sB.map (embTV : FTy → FLV.Ty α)) =
      (FTy.tappStep k A B sA sB).map embTV := by
  cases A with
  | lam k' A₀ => exact absurd rfl (hA k' A₀)
  | tvar _ | arr _ _ | all _ _ | app _ _ _ =>
      cases sA with
      | some A' => rfl
      | none => cases sB <;> rfl

omit [FL.AtomOrder α] in
theorem tstep_embTV : ∀ A : FTy, FLV.tstep (embTV A : FLV.Ty α) = (FTy.tstep A).map embTV
  | .tvar _ => rfl
  | .arr A B => by
      show (match FLV.tstep (embTV A : FLV.Ty α) with
        | some A' => some (FLV.Ty.arr A' (embTV B))
        | none => (FLV.tstep (embTV B : FLV.Ty α)).map (FLV.Ty.arr (embTV A))) =
        (match FTy.tstep A with
          | some A' => some (FTy.arr A' B)
          | none => (FTy.tstep B).map (FTy.arr A)).map embTV
      rw [tstep_embTV A, tstep_embTV B]
      cases FTy.tstep A with
      | some A' => rfl
      | none => cases FTy.tstep B <;> rfl
  | .all k A => by
      show (FLV.tstep (embTV A : FLV.Ty α)).map (FLV.Ty.all (embKV k)) =
        ((FTy.tstep A).map (FTy.all k)).map embTV
      rw [tstep_embTV A]; cases FTy.tstep A <;> rfl
  | .lam k A => by
      show (FLV.tstep (embTV A : FLV.Ty α)).map (FLV.Ty.lam (embKV k)) =
        ((FTy.tstep A).map (FTy.lam k)).map embTV
      rw [tstep_embTV A]; cases FTy.tstep A <;> rfl
  | .app k A B => by
      show FLV.tappStep (embKV k) (embTV A) (embTV B) (FLV.tstep (embTV A : FLV.Ty α))
          (FLV.tstep (embTV B : FLV.Ty α)) =
        (FTy.tappStep k A B (FTy.tstep A) (FTy.tstep B)).map embTV
      rw [tstep_embTV A, tstep_embTV B]
      cases A with
      | lam k' A₀ =>
          show some (FLV.Ty.inst (embTV A₀) (embTV B)) = some (embTV (FTy.inst A₀ B))
          rw [embTV_inst]
      | tvar _ => exact tappStep_embTV k _ B _ _ (fun _ _ h => FTy.noConfusion h)
      | arr _ _ => exact tappStep_embTV k _ B _ _ (fun _ _ h => FTy.noConfusion h)
      | all _ _ => exact tappStep_embTV k _ B _ _ (fun _ _ h => FTy.noConfusion h)
      | app _ _ _ => exact tappStep_embTV k _ B _ _ (fun _ _ h => FTy.noConfusion h)

omit [FL.AtomOrder α] in
theorem tnf_embTV : ∀ (n : Nat) (A : FTy), FLV.tnf n (embTV A : FLV.Ty α) = embTV (FTy.tnf n A)
  | 0, _ => rfl
  | n + 1, A => by
      show (match FLV.tstep (embTV A : FLV.Ty α) with
        | some B => FLV.tnf n B
        | none => embTV A) = embTV (match FTy.tstep A with
          | some B => FTy.tnf n B
          | none => A)
      rw [tstep_embTV A]
      cases FTy.tstep A with
      | some B => exact tnf_embTV n B
      | none => rfl

omit [FL.AtomOrder α] in
/-- With enough fuel the ladder with levels normalizes an embedded type to `tnf F₀`. -/
theorem tnf_embTV_stable {F₀ fuel : Nat} (hF : F₀ ≤ fuel) {A : FTy}
    (hA : FTy.tstep (FTy.tnf F₀ A) = none) :
    FLV.tnf fuel (embTV A : FLV.Ty α) = embTV (FTy.tnf F₀ A) := by
  rw [tnf_embTV, show fuel = F₀ + (fuel - F₀) by omega]
  rw [tnf_stable F₀ rfl hA (fuel - F₀)]

omit [FL.AtomOrder α] in
theorem tnf_eqV {A : FLV.Ty α} (h : FLV.tstep A = none) : ∀ fuel, FLV.tnf fuel A = A
  | 0 => rfl
  | _ + 1 => by simp only [FLV.tnf, h]

theorem kind_embTV : ∀ (A : FTy) {Δ : List FK} {k : FK} (Λ : List (FLV.Lvl α))
    (D : List (FLV.Kind α)),
    inferKindF Δ A = some k → FLV.inferKind Λ (Δ.map embKV ++ D) (embTV A) = some (embKV k)
  | .tvar n, Δ, k, Λ, D, h => by
      show nth? (Δ.map embKV ++ D) n = _
      exact nth?_append_left (nth?_map_some embKV h)
  | .arr A B, Δ, k, Λ, D, h => by
      cases hA : inferKindF Δ A with
      | none => simp [inferKindF, hA, arrKF, starKF] at h
      | some kA =>
          cases hB : inferKindF Δ B with
          | none => cases kA <;> simp [inferKindF, hA, hB, arrKF, starKF] at h
          | some kB =>
              cases kA with
              | arr _ _ => simp [inferKindF, hA, hB, arrKF, starKF] at h
              | star =>
                  cases kB with
                  | arr _ _ => simp [inferKindF, hA, hB, arrKF, starKF] at h
                  | star =>
                      have hk : k = .star := by
                        simp [inferKindF, hA, hB, arrKF, starKF] at h; exact h.symm
                      subst hk
                      show FLV.arrK (FLV.inferKind Λ (Δ.map embKV ++ D) (embTV A))
                        (FLV.inferKind Λ (Δ.map embKV ++ D) (embTV B)) = _
                      rw [kind_embTV A Λ D hA, kind_embTV B Λ D hB]; rfl
  | .all k' A, Δ, k, Λ, D, h => by
      cases hA : inferKindF (k' :: Δ) A with
      | none => simp [inferKindF, hA, starKF] at h
      | some kA =>
          cases kA with
          | arr _ _ => simp [inferKindF, hA, starKF] at h
          | star =>
              have hk : k = .star := by simp [inferKindF, hA, starKF] at h; exact h.symm
              subst hk
              show FLV.starK (FLV.inferKind Λ (embKV k' :: (Δ.map embKV ++ D)) (embTV A)) = _
              rw [show embKV k' :: (Δ.map embKV ++ D) = (k' :: Δ).map embKV ++ D from rfl,
                kind_embTV A Λ D hA]; rfl
  | .lam k' A, Δ, k, Λ, D, h => by
      cases hA : inferKindF (k' :: Δ) A with
      | none => simp [inferKindF, hA] at h
      | some kA =>
          have hk : k = .arr k' kA := by simp [inferKindF, hA] at h; exact h.symm
          subst hk
          show (FLV.inferKind Λ (embKV k' :: (Δ.map embKV ++ D)) (embTV A)).map
            (FLV.Kind.arr (embKV k')) = _
          rw [show embKV k' :: (Δ.map embKV ++ D) = (k' :: Δ).map embKV ++ D from rfl,
            kind_embTV A Λ D hA]; rfl
  | .app k' A B, Δ, k, Λ, D, h => by
      cases hA : inferKindF Δ A with
      | none => simp [inferKindF, hA, appKF] at h
      | some kA =>
          cases hB : inferKindF Δ B with
          | none => cases kA <;> simp [inferKindF, hA, hB, appKF] at h
          | some kB =>
              cases kA with
              | star => simp [inferKindF, hA, hB, appKF] at h
              | arr k₁ k₂ =>
                  have h' : k₁ = k' ∧ kB = k' ∧ k = k₂ := by
                    simp only [inferKindF, hA, hB, appKF] at h
                    split at h
                    · next hc => cases h; exact ⟨hc.1, hc.2, rfl⟩
                    · cases h
                  obtain ⟨e1, e2, e3⟩ := h'
                  show FLV.appK (embKV k') (FLV.inferKind Λ (Δ.map embKV ++ D) (embTV A))
                    (FLV.inferKind Λ (Δ.map embKV ++ D) (embTV B)) = _
                  rw [kind_embTV A Λ D hA, kind_embTV B Λ D hB, e1, e2, e3]
                  show (if embKV k' = embKV k' ∧ embKV k' = embKV k' then some (embKV k₂)
                    else none) = _
                  simp only [and_self, ↓reduceIte]

omit [DecidableEq α] [FL.AtomOrder α] in
theorem map_ren_embTV (Γ : List FTy) (G : List (FLV.Ty α)) :
    (Γ.map embTV ++ G).map (FLV.Ty.tren Nat.succ) =
      (Γ.map (FTy.ren Nat.succ)).map embTV ++ G.map (FLV.Ty.tren Nat.succ) := by
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro A _
  exact (embTV_ren A Nat.succ).symm

/-- **Soundness of `checkW` for the ladder with levels**, at every fuel `≥ F₀`, in
every level context and every extension of the contexts. -/
theorem checkW_soundV (F₀ : Nat) : ∀ (t : FTm) {Δ : List FK} {Γ : List FTy} {T : FTy},
    checkW F₀ Δ Γ t = some T → ∀ {fuel : Nat}, F₀ ≤ fuel →
    ∀ (Λ : List (FLV.Lvl α)) (D : List (FLV.Kind α)) (G : List (FLV.Ty α)),
    FLV.infer fuel Λ (Δ.map embKV ++ D) (Γ.map embTV ++ G) (embCV t) = some (embTV T)
  | .var n, Δ, Γ, T, h, fuel, _, Λ, D, G => by
      show nth? (Γ.map embTV ++ G) n = _
      exact nth?_append_left (nth?_map_some embTV h)
  | .lam A b, Δ, Γ, T, h, fuel, hF, Λ, D, G => by
      simp only [checkW] at h
      split at h
      · next hA =>
          cases hb : checkW F₀ Δ (A :: Γ) b with
          | none => rw [hb] at h; cases h
          | some B =>
              rw [hb] at h
              cases h
              have ih := checkW_soundV F₀ b hb hF Λ D G
              show (match FLV.inferKind Λ (Δ.map embKV ++ D) (embTV A) with
                | some .star =>
                    (FLV.infer fuel Λ (Δ.map embKV ++ D) (embTV A :: (Γ.map embTV ++ G))
                      (embCV b)).map (FLV.Ty.arr (embTV A))
                | _ => none) = _
              rw [kind_embTV A Λ D hA]
              show (FLV.infer fuel Λ (Δ.map embKV ++ D) ((A :: Γ).map embTV ++ G)
                (embCV b)).map (FLV.Ty.arr (embTV A)) = _
              rw [ih]
              rfl
      · cases h
  | .app t u, Δ, Γ, T, h, fuel, hF, Λ, D, G => by
      cases ht : checkW F₀ Δ Γ t with
      | none => simp only [checkW, ht] at h; cases h
      | some T₁ =>
          cases hu : checkW F₀ Δ Γ u with
          | none => simp only [checkW, ht, hu] at h; cases h
          | some U =>
              cases hT : FTy.tnf F₀ T₁ with
              | arr A B =>
                  simp only [checkW, ht, hu, hT] at h
                  split at h
                  · next hc =>
                      cases h
                      obtain ⟨hn1, hn2, hAU⟩ := hc
                      have hs1 := tstep_none_of_normalB hn1
                      have hs2 := tstep_none_of_normalB hn2
                      show (match FLV.infer fuel Λ (Δ.map embKV ++ D) (Γ.map embTV ++ G) (embCV t),
                          FLV.infer fuel Λ (Δ.map embKV ++ D) (Γ.map embTV ++ G) (embCV u) with
                        | some T, some U => FLV.appResult fuel T U
                        | _, _ => none) = _
                      rw [checkW_soundV F₀ t ht hF Λ D G, checkW_soundV F₀ u hu hF Λ D G]
                      show (match FLV.tnf fuel (embTV T₁ : FLV.Ty α) with
                        | FLV.Ty.arr A B =>
                            if FLV.tnf fuel A = FLV.tnf fuel (embTV U) then some B else none
                        | _ => none) = _
                      rw [tnf_embTV_stable hF (hT ▸ hs1), hT,
                        tnf_embTV_stable hF hs2, ← hAU]
                      have hsA : FLV.tstep (embTV A : FLV.Ty α) = none := by
                        rw [tstep_embTV, tstep_arr_left hs1]; rfl
                      show (if FLV.tnf fuel (embTV A : FLV.Ty α) = embTV A then some _ else none) = _
                      rw [tnf_eqV hsA]
                      simp only [↓reduceIte]
                  · cases h
              | tvar _ => simp only [checkW, ht, hu, hT] at h; cases h
              | all _ _ => simp only [checkW, ht, hu, hT] at h; cases h
              | lam _ _ => simp only [checkW, ht, hu, hT] at h; cases h
              | app _ _ _ => simp only [checkW, ht, hu, hT] at h; cases h
  | .tlam k b, Δ, Γ, T, h, fuel, hF, Λ, D, G => by
      simp only [checkW] at h
      cases hb : checkW F₀ (k :: Δ) (Γ.map (FTy.ren Nat.succ)) b with
      | none => rw [hb] at h; cases h
      | some B =>
          rw [hb] at h
          cases h
          have ih := checkW_soundV F₀ b hb hF Λ D (G.map (FLV.Ty.tren Nat.succ))
          rw [← map_ren_embTV] at ih
          show (FLV.infer fuel Λ (embKV k :: (Δ.map embKV ++ D))
            ((Γ.map embTV ++ G).map (FLV.Ty.tren Nat.succ)) (embCV b)).map
              (FLV.Ty.all (embKV k)) = _
          rw [show embKV k :: (Δ.map embKV ++ D) = (k :: Δ).map embKV ++ D from rfl, ih]
          rfl
  | .tapp t B, Δ, Γ, T, h, fuel, hF, Λ, D, G => by
      cases ht : checkW F₀ Δ Γ t with
      | none => simp only [checkW, ht] at h; cases h
      | some T₁ =>
          cases hT : FTy.tnf F₀ T₁ with
          | all k A =>
              simp only [checkW, ht, hT] at h
              split at h
              · next hc =>
                  cases h
                  have hs1 := tstep_none_of_normalB hc.1
                  show (match FLV.infer fuel Λ (Δ.map embKV ++ D) (Γ.map embTV ++ G) (embCV t) with
                    | some T => FLV.tappResult fuel Λ (Δ.map embKV ++ D) T (embTV B)
                    | none => none) = _
                  rw [checkW_soundV F₀ t ht hF Λ D G]
                  show (match FLV.tnf fuel (embTV T₁ : FLV.Ty α) with
                    | FLV.Ty.all k A =>
                        if FLV.inferKind Λ (Δ.map embKV ++ D) (embTV B) = some k
                        then some (FLV.Ty.inst A (embTV B)) else none
                    | _ => none) = _
                  rw [tnf_embTV_stable hF (hT ▸ hs1), hT]
                  show (if FLV.inferKind Λ (Δ.map embKV ++ D) (embTV B) = some (embKV k)
                    then some (FLV.Ty.inst (embTV A) (embTV B)) else none) = _
                  rw [kind_embTV B Λ D hc.2, embTV_inst]
                  simp only [↓reduceIte]
              · cases h
          | tvar _ => simp only [checkW, ht, hT] at h; cases h
          | arr _ _ => simp only [checkW, ht, hT] at h; cases h
          | lam _ _ => simp only [checkW, ht, hT] at h; cases h
          | app _ _ _ => simp only [checkW, ht, hT] at h; cases h

/-! ## Closedness -/

theorem nth?_lt {β : Type} : ∀ {Γ : List β} {n : Nat} {x : β}, nth? Γ n = some x → n < Γ.length
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, _ => Nat.succ_pos _
  | _ :: Γ, n + 1, _, h => Nat.succ_lt_succ (nth?_lt (Γ := Γ) (n := n) h)

omit [DecidableEq α] [FL.AtomOrder α] in
/-- A program that `checkW` accepts is closed relative to its context. -/
theorem closedB_eraseF {F₀ : Nat} : ∀ (t : FTm) {Δ : List FK} {Γ : List FTy} {T : FTy},
    checkW F₀ Δ Γ t = some T → FT2.closedB Γ.length (FT2.embF (eraseF t)) = true
  | .var n, Δ, Γ, T, h => by
      show decide (n < Γ.length) = true
      exact decide_eq_true (nth?_lt (show nth? Γ n = some T from h))
  | .lam A b, Δ, Γ, T, h => by
      simp only [checkW] at h
      split at h
      · cases hb : checkW F₀ Δ (A :: Γ) b with
        | none => rw [hb] at h; cases h
        | some B => exact closedB_eraseF b hb
      · cases h
  | .app t u, Δ, Γ, T, h => by
      cases ht : checkW F₀ Δ Γ t with
      | none => simp only [checkW, ht] at h; cases h
      | some T₁ =>
          cases hu : checkW F₀ Δ Γ u with
          | none => simp only [checkW, ht, hu] at h; cases h
          | some U =>
              show (FT2.closedB Γ.length (FT2.embF (eraseF t)) &&
                FT2.closedB Γ.length (FT2.embF (eraseF u))) = true
              rw [closedB_eraseF t ht, closedB_eraseF u hu]
              rfl
  | .tlam k b, Δ, Γ, T, h => by
      simp only [checkW] at h
      cases hb : checkW F₀ (k :: Δ) (Γ.map (FTy.ren Nat.succ)) b with
      | none => rw [hb] at h; cases h
      | some B =>
          have := closedB_eraseF b hb
          rw [List.length_map] at this
          exact this
  | .tapp t B, Δ, Γ, T, h => by
      cases ht : checkW F₀ Δ Γ t with
      | none => simp only [checkW, ht] at h; cases h
      | some T₁ => exact closedB_eraseF t ht

end BusyLean.Indep.FW
