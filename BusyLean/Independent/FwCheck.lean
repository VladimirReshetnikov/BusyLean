import BusyLean.Independent.SystemTLtLadder

/-!
# A verified type checker for the Fω fragment (proof infrastructure)

The **Fω** fragment of the ladder language: kinds `★` and `κ → κ`, type-level
λ and application, `∀` over any kind. The syntax `FTy`/`FTm` has no atoms, so
the typing of a concrete program is a kernel computation (`checkW`) that does
not depend on the atom type.

`checkW F₀` normalizes types with the ladder's own reduction strategy
(`tstepF` mirrors `FL.tstep`) for `F₀` steps and demands normal forms, so its
verdict holds for the ladder's checker at every fuel `≥ F₀` (`checkW_sound`).
`mem_ctmsUpTo` shows that embedded programs of small depth are enumerated.
-/

namespace BusyLean.Indep.FW

open BusyLean.FL
open BusyLean.Fw (nth?)
open BusyLean.F.Tm (upRen)

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

/-- Kinds without atoms. -/
inductive FK where
  | star : FK
  | arr : FK → FK → FK
  deriving DecidableEq, Repr

/-- Fω types without atoms. -/
inductive FTy where
  | tvar : Nat → FTy
  | arr : FTy → FTy → FTy
  | all : FK → FTy → FTy
  | lam : FK → FTy → FTy
  | app : FK → FTy → FTy → FTy
  deriving DecidableEq, Repr

/-- Church-style Fω terms without atoms. -/
inductive FTm where
  | var : Nat → FTm
  | lam : FTy → FTm → FTm
  | app : FTm → FTm → FTm
  | tlam : FK → FTm → FTm
  | tapp : FTm → FTy → FTm
  deriving Repr

/-! ## Embedding into the ladder language -/

variable {α : Type}

def embK : FK → Kind α
  | .star => .star
  | .arr a b => .arr (embK a) (embK b)

def embT : FTy → FL.Ty α
  | .tvar n => .tvar n
  | .arr A B => .arr (embT A) (embT B)
  | .all k A => .all (embK k) (embT A)
  | .lam k A => .lam (embK k) (embT A)
  | .app k A B => .app (embK k) (embT A) (embT B)

def embC : FTm → CTm α
  | .var n => .var n
  | .lam A b => .lam (embT A) (embC b)
  | .app t u => .app (embC t) (embC u)
  | .tlam k b => .tlam (embK k) (embC b)
  | .tapp t A => .tapp (embC t) (embT A)

/-- The erasure of an `FTm`. -/
def eraseF : FTm → F.Tm
  | .var n => .var n
  | .lam _ b => .lam (eraseF b)
  | .app t u => .app (eraseF t) (eraseF u)
  | .tlam _ b => eraseF b
  | .tapp t _ => eraseF t

theorem erase_embC [DecidableEq α] [AtomOrder α] :
    ∀ t : FTm, FL.erase (embC t : CTm α) = eraseF t
  | .var _ => rfl
  | .lam _ b => congrArg F.Tm.lam (erase_embC b)
  | .app t u => by
      show F.Tm.app (FL.erase (embC t : CTm α)) (FL.erase (embC u : CTm α)) = _
      rw [erase_embC t, erase_embC u]; rfl
  | .tlam _ b => erase_embC b
  | .tapp t _ => erase_embC t

theorem embK_inj : ∀ {a b : FK}, (embK a : Kind α) = embK b → a = b
  | .star, .star, _ => rfl
  | .arr a₁ a₂, .arr b₁ b₂, h => by
      simp only [embK, Kind.arr.injEq] at h
      rw [embK_inj h.1, embK_inj h.2]
  | .star, .arr _ _, h => by simp [embK] at h
  | .arr _ _, .star, h => by simp [embK] at h

/-! ## Depths and enumeration -/

def kdepthF : FK → Nat
  | .star => 1
  | .arr a b => max (kdepthF a) (kdepthF b) + 1

def tdepthF : FTy → Nat
  | .tvar n => n + 2
  | .arr A B => max (tdepthF A) (tdepthF B) + 1
  | .all k A => max (kdepthF k) (tdepthF A) + 1
  | .lam k A => max (kdepthF k) (tdepthF A) + 1
  | .app k A B => max (kdepthF k) (max (tdepthF A) (tdepthF B)) + 1

def cdepthF : FTm → Nat
  | .var n => n + 2
  | .lam A e => max (tdepthF A) (cdepthF e) + 1
  | .app t u => max (cdepthF t) (cdepthF u) + 1
  | .tlam k e => max (kdepthF k) (cdepthF e) + 1
  | .tapp e A => max (cdepthF e) (tdepthF A) + 1

open BusyLean.Indep.Ladder (kindsUpTo tysUpTo ctmsUpTo cross natsUpTo)
open BusyLean.Indep.Emb (mem_cross)

theorem mem_kindsUpTo (as : List α) : ∀ (k : FK) {m : Nat}, kdepthF k ≤ m →
    (embK k : Kind α) ∈ kindsUpTo as m
  | .star, m + 1, _ => List.mem_cons_self
  | .arr a b, m + 1, h => by
      simp only [kdepthF] at h
      refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun p : Kind α × Kind α => Kind.arr p.1 p.2) (mem_cross ?_ ?_))))
      · exact mem_kindsUpTo as a (by omega)
      · exact mem_kindsUpTo as b (by omega)
  | .star, 0, h => absurd h (by decide)
  | .arr _ _, 0, h => absurd h (Nat.not_succ_le_zero _)

theorem mem_tysUpTo (as : List α) : ∀ (A : FTy) {m : Nat}, tdepthF A ≤ m →
    (embT A : FL.Ty α) ∈ tysUpTo as m
  | .tvar n, m + 1, h =>
      List.mem_append_left _ (List.mem_map_of_mem (f := FL.Ty.tvar)
        (Emb.mem_natsUpTo (show n < m by simp only [tdepthF] at h; omega)))
  | .arr A B, m + 1, h => by
      simp only [tdepthF] at h
      refine List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem
        (f := fun p : FL.Ty α × FL.Ty α => FL.Ty.arr p.1 p.2) (mem_cross ?_ ?_)))
      · exact mem_tysUpTo as A (by omega)
      · exact mem_tysUpTo as B (by omega)
  | .all k A, m + 1, h => by
      simp only [tdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun p : Kind α × FL.Ty α => FL.Ty.all p.1 p.2)
          (mem_cross (mem_kindsUpTo as k (by omega)) (mem_tysUpTo as A (by omega))))))
  | .lam k A, m + 1, h => by
      simp only [tdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ (List.mem_map_of_mem (f := fun p : Kind α × FL.Ty α => FL.Ty.lam p.1 p.2)
          (mem_cross (mem_kindsUpTo as k (by omega)) (mem_tysUpTo as A (by omega)))))))
  | .app k A B, m + 1, h => by
      simp only [tdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _
          (List.mem_map_of_mem (f := fun p : Kind α × (FL.Ty α × FL.Ty α) => FL.Ty.app p.1 p.2.1 p.2.2)
            (mem_cross (mem_kindsUpTo as k (by omega))
              (mem_cross (mem_tysUpTo as A (by omega)) (mem_tysUpTo as B (by omega)))))))))
  | .tvar _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .arr _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .all _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .lam _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .app _ _ _, 0, h => absurd h (Nat.not_succ_le_zero _)

theorem mem_ctmsUpTo (as : List α) : ∀ (e : FTm) {m : Nat}, cdepthF e ≤ m →
    (embC e : CTm α) ∈ ctmsUpTo as m
  | .var n, m + 1, h =>
      List.mem_append_left _ (List.mem_map_of_mem (f := CTm.var)
        (Emb.mem_natsUpTo (show n < m by simp only [cdepthF] at h; omega)))
  | .lam A e, m + 1, h => by
      simp only [cdepthF] at h
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem
        (f := fun p : FL.Ty α × CTm α => CTm.lam p.1 p.2)
        (mem_cross (mem_tysUpTo as A (by omega)) (mem_ctmsUpTo as e (by omega)))))
  | .app t u, m + 1, h => by
      simp only [cdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun p : CTm α × CTm α => CTm.app p.1 p.2)
        (mem_cross (mem_ctmsUpTo as t (by omega)) (mem_ctmsUpTo as u (by omega))))))
  | .tlam k e, m + 1, h => by
      simp only [cdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ (List.mem_map_of_mem (f := fun p : Kind α × CTm α => CTm.tlam p.1 p.2)
          (mem_cross (mem_kindsUpTo as k (by omega)) (mem_ctmsUpTo as e (by omega)))))))
  | .tapp e A, m + 1, h => by
      simp only [cdepthF] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _
          (List.mem_map_of_mem (f := fun p : CTm α × FL.Ty α => CTm.tapp p.1 p.2)
            (mem_cross (mem_ctmsUpTo as e (by omega)) (mem_tysUpTo as A (by omega))))))))
  | .var _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .lam _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .app _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .tlam _ _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | .tapp _ _, 0, h => absurd h (Nat.not_succ_le_zero _)

/-! ## Types: the ladder's operations, mirrored -/

namespace FTy

def ren (ξ : Nat → Nat) : FTy → FTy
  | tvar n => tvar (ξ n)
  | arr A B => arr (ren ξ A) (ren ξ B)
  | all k A => all k (ren (upRen ξ) A)
  | lam k A => lam k (ren (upRen ξ) A)
  | app k A B => app k (ren ξ A) (ren ξ B)

def up (σ : Nat → FTy) : Nat → FTy
  | 0 => tvar 0
  | n + 1 => ren Nat.succ (σ n)

def subst (σ : Nat → FTy) : FTy → FTy
  | tvar n => σ n
  | arr A B => arr (subst σ A) (subst σ B)
  | all k A => all k (subst (up σ) A)
  | lam k A => lam k (subst (up σ) A)
  | app k A B => app k (subst σ A) (subst σ B)

def cons (B : FTy) (σ : Nat → FTy) : Nat → FTy
  | 0 => B
  | n + 1 => σ n

def inst (A B : FTy) : FTy := subst (cons B tvar) A

def tappCong (k : FK) (A B : FTy) (sA sB : Option FTy) : Option FTy :=
  match sA with
  | some A' => some (app k A' B)
  | none => sB.map (app k A)

def tappStep (k : FK) (A B : FTy) (sA sB : Option FTy) : Option FTy :=
  match A with
  | lam _ A₀ => some (inst A₀ B)
  | _ => tappCong k A B sA sB

/-- One step of type reduction, by the ladder's strategy. -/
def tstep : FTy → Option FTy
  | tvar _ => none
  | arr A B =>
      match tstep A with
      | some A' => some (arr A' B)
      | none => (tstep B).map (arr A)
  | all k A => (tstep A).map (all k)
  | lam k A => (tstep A).map (lam k)
  | app k A B => tappStep k A B (tstep A) (tstep B)

def tnf : Nat → FTy → FTy
  | 0, A => A
  | fuel + 1, A =>
      match tstep A with
      | some B => tnf fuel B
      | none => A

end FTy

def starKF : Option FK → Option FK
  | some .star => some .star
  | _ => none

def arrKF (x y : Option FK) : Option FK := (starKF x).bind fun _ => starKF y

def appKF (k : FK) : Option FK → Option FK → Option FK
  | some (.arr k₁ k₂), some k' => if k₁ = k ∧ k' = k then some k₂ else none
  | _, _ => none

def inferKindF : List FK → FTy → Option FK
  | Δ, .tvar n => nth? Δ n
  | Δ, .arr A B => arrKF (inferKindF Δ A) (inferKindF Δ B)
  | Δ, .all k A => starKF (inferKindF (k :: Δ) A)
  | Δ, .lam k A => (inferKindF (k :: Δ) A).map (FK.arr k)
  | Δ, .app k A B => appKF k (inferKindF Δ A) (inferKindF Δ B)

/-! ## Commutation with the embedding -/

theorem embT_ren : ∀ (A : FTy) (ξ : Nat → Nat), embT (A.ren ξ) = Ty.tren ξ (embT A : FL.Ty α)
  | .tvar _, _ => rfl
  | .arr A B, ξ => by
      show FL.Ty.arr (embT (A.ren ξ)) (embT (B.ren ξ)) = _
      rw [embT_ren A ξ, embT_ren B ξ]; rfl
  | .all k A, ξ => by
      show FL.Ty.all (embK k) (embT (A.ren (upRen ξ))) = _
      rw [embT_ren A (upRen ξ)]; rfl
  | .lam k A, ξ => by
      show FL.Ty.lam (embK k) (embT (A.ren (upRen ξ))) = _
      rw [embT_ren A (upRen ξ)]; rfl
  | .app k A B, ξ => by
      show FL.Ty.app (embK k) (embT (A.ren ξ)) (embT (B.ren ξ)) = _
      rw [embT_ren A ξ, embT_ren B ξ]; rfl

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
  | .all k A, σ => by
      show FL.Ty.all (embK k) (embT (A.subst (FTy.up σ))) = _
      rw [embT_subst A (FTy.up σ), embT_up σ]; rfl
  | .lam k A, σ => by
      show FL.Ty.lam (embK k) (embT (A.subst (FTy.up σ))) = _
      rw [embT_subst A (FTy.up σ), embT_up σ]; rfl
  | .app k A B, σ => by
      show FL.Ty.app (embK k) (embT (A.subst σ)) (embT (B.subst σ)) = _
      rw [embT_subst A σ, embT_subst B σ]; rfl

theorem embT_inst (A B : FTy) : embT (A.inst B) = Ty.inst (embT A : FL.Ty α) (embT B) := by
  show embT (A.subst (FTy.cons B FTy.tvar)) = _
  rw [embT_subst]
  show Ty.tsubst (fun n => embT (FTy.cons B FTy.tvar n)) (embT A) =
    Ty.tsubst (Ty.tcons (embT B) Ty.tvar) (embT A)
  congr 1
  funext n
  cases n <;> rfl

variable [DecidableEq α] [AtomOrder α]

omit [DecidableEq α] [AtomOrder α] in
theorem tappStep_embT (k : FK) (A B : FTy) (sA sB : Option FTy)
    (hA : ∀ k' A₀, A ≠ FTy.lam k' A₀) :
    tappStep (embK k) (embT A) (embT B) (sA.map embT) (sB.map (embT : FTy → FL.Ty α)) =
      (FTy.tappStep k A B sA sB).map embT := by
  cases A with
  | lam k' A₀ => exact absurd rfl (hA k' A₀)
  | tvar _ | arr _ _ | all _ _ | app _ _ _ =>
      cases sA with
      | some A' => rfl
      | none => cases sB <;> rfl

theorem tstep_embT : ∀ A : FTy, tstep (embT A : FL.Ty α) = (FTy.tstep A).map embT
  | .tvar _ => rfl
  | .arr A B => by
      show (match tstep (embT A : FL.Ty α) with
        | some A' => some (FL.Ty.arr A' (embT B))
        | none => (tstep (embT B : FL.Ty α)).map (FL.Ty.arr (embT A))) =
        (match FTy.tstep A with
          | some A' => some (FTy.arr A' B)
          | none => (FTy.tstep B).map (FTy.arr A)).map embT
      rw [tstep_embT A, tstep_embT B]
      cases FTy.tstep A with
      | some A' => rfl
      | none => cases FTy.tstep B <;> rfl
  | .all k A => by
      show (tstep (embT A : FL.Ty α)).map (FL.Ty.all (embK k)) = ((FTy.tstep A).map (FTy.all k)).map embT
      rw [tstep_embT A]; cases FTy.tstep A <;> rfl
  | .lam k A => by
      show (tstep (embT A : FL.Ty α)).map (FL.Ty.lam (embK k)) = ((FTy.tstep A).map (FTy.lam k)).map embT
      rw [tstep_embT A]; cases FTy.tstep A <;> rfl
  | .app k A B => by
      show tappStep (embK k) (embT A) (embT B) (tstep (embT A : FL.Ty α)) (tstep (embT B : FL.Ty α)) =
        (FTy.tappStep k A B (FTy.tstep A) (FTy.tstep B)).map embT
      rw [tstep_embT A, tstep_embT B]
      cases A with
      | lam k' A₀ =>
          show some (Ty.inst (embT A₀) (embT B)) = some (embT (FTy.inst A₀ B))
          rw [embT_inst]
      | tvar _ => exact tappStep_embT k _ B _ _ (fun _ _ h => FTy.noConfusion h)
      | arr _ _ => exact tappStep_embT k _ B _ _ (fun _ _ h => FTy.noConfusion h)
      | all _ _ => exact tappStep_embT k _ B _ _ (fun _ _ h => FTy.noConfusion h)
      | app _ _ _ => exact tappStep_embT k _ B _ _ (fun _ _ h => FTy.noConfusion h)

theorem tnf_embT : ∀ (n : Nat) (A : FTy), tnf n (embT A : FL.Ty α) = embT (FTy.tnf n A)
  | 0, _ => rfl
  | n + 1, A => by
      show (match tstep (embT A : FL.Ty α) with
        | some B => tnf n B
        | none => embT A) = embT (match FTy.tstep A with
          | some B => FTy.tnf n B
          | none => A)
      rw [tstep_embT A]
      cases FTy.tstep A with
      | some B => exact tnf_embT n B
      | none => rfl

/-- Once normal, more fuel changes nothing. -/
theorem tnf_stable : ∀ (n : Nat) {A A' : FTy}, FTy.tnf n A = A' → FTy.tstep A' = none →
    ∀ k, FTy.tnf (n + k) A = A'
  | 0, A, A', h, hA', k => by
      subst h
      rw [Nat.zero_add]
      cases k with
      | zero => rfl
      | succ k =>
          have hA'' : FTy.tstep A = none := hA'
          show (match FTy.tstep A with | some B => FTy.tnf k B | none => A) = A
          rw [hA'']
  | n + 1, A, A', h, hA', k => by
      rw [show n + 1 + k = (n + k) + 1 by omega]
      show (match FTy.tstep A with | some B => FTy.tnf (n + k) B | none => A) = A'
      have h' : (match FTy.tstep A with | some B => FTy.tnf n B | none => A) = A' := h
      cases hs : FTy.tstep A with
      | some B => rw [hs] at h'; exact tnf_stable n h' hA' k
      | none => rw [hs] at h'; exact h'

theorem kind_embT : ∀ (A : FTy) {Δ : List FK} {k : FK} (D : List (Kind α)),
    inferKindF Δ A = some k → inferKind (Δ.map embK ++ D) (embT A) = some (embK k)
  | .tvar n, Δ, k, D, h => by
      show nth? (Δ.map embK ++ D) n = _
      exact nth?_append_left (nth?_map_some embK h)
  | .arr A B, Δ, k, D, h => by
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
                      show arrK (inferKind (Δ.map embK ++ D) (embT A))
                        (inferKind (Δ.map embK ++ D) (embT B)) = _
                      rw [kind_embT A D hA, kind_embT B D hB]; rfl
  | .all k' A, Δ, k, D, h => by
      cases hA : inferKindF (k' :: Δ) A with
      | none => simp [inferKindF, hA, starKF] at h
      | some kA =>
          cases kA with
          | arr _ _ => simp [inferKindF, hA, starKF] at h
          | star =>
              have hk : k = .star := by simp [inferKindF, hA, starKF] at h; exact h.symm
              subst hk
              show starK (inferKind (embK k' :: (Δ.map embK ++ D)) (embT A)) = _
              rw [show embK k' :: (Δ.map embK ++ D) = (k' :: Δ).map embK ++ D from rfl,
                kind_embT A D hA]; rfl
  | .lam k' A, Δ, k, D, h => by
      cases hA : inferKindF (k' :: Δ) A with
      | none => simp [inferKindF, hA] at h
      | some kA =>
          have hk : k = .arr k' kA := by simp [inferKindF, hA] at h; exact h.symm
          subst hk
          show (inferKind (embK k' :: (Δ.map embK ++ D)) (embT A)).map (Kind.arr (embK k')) = _
          rw [show embK k' :: (Δ.map embK ++ D) = (k' :: Δ).map embK ++ D from rfl,
            kind_embT A D hA]; rfl
  | .app k' A B, Δ, k, D, h => by
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
                  show appK (embK k') (inferKind (Δ.map embK ++ D) (embT A))
                    (inferKind (Δ.map embK ++ D) (embT B)) = _
                  rw [kind_embT A D hA, kind_embT B D hB, e1, e2, e3]
                  show (if embK k' = embK k' ∧ embK k' = embK k' then some (embK k₂) else none) = _
                  simp only [and_self, ↓reduceIte]

/-! ## The checker and its soundness -/

/-- `A` is in normal form. -/
def normalB (A : FTy) : Bool := (FTy.tstep A).isNone

/-- The type checker: types are normalized for `F₀` steps, and must then be normal. -/
def checkW (F₀ : Nat) : List FK → List FTy → FTm → Option FTy
  | _, Γ, .var n => nth? Γ n
  | Δ, Γ, .lam A b =>
      if inferKindF Δ A = some .star then (checkW F₀ Δ (A :: Γ) b).map (FTy.arr A) else none
  | Δ, Γ, .app t u =>
      match checkW F₀ Δ Γ t, checkW F₀ Δ Γ u with
      | some T, some U =>
          match FTy.tnf F₀ T with
          | .arr A B =>
              if normalB (.arr A B) = true ∧ normalB (FTy.tnf F₀ U) = true ∧ A = FTy.tnf F₀ U
              then some B else none
          | _ => none
      | _, _ => none
  | Δ, Γ, .tlam k b => (checkW F₀ (k :: Δ) (Γ.map (FTy.ren Nat.succ)) b).map (FTy.all k)
  | Δ, Γ, .tapp t B =>
      match checkW F₀ Δ Γ t with
      | some T =>
          match FTy.tnf F₀ T with
          | .all k A =>
              if normalB (.all k A) = true ∧ inferKindF Δ B = some k then some (FTy.inst A B)
              else none
          | _ => none
      | none => none

theorem tstep_none_of_normalB {A : FTy} (h : normalB A = true) : FTy.tstep A = none := by
  unfold normalB at h
  cases e : FTy.tstep A with
  | none => rfl
  | some _ => rw [e] at h; cases h

theorem tstep_arr_left {A B : FTy} (h : FTy.tstep (.arr A B) = none) : FTy.tstep A = none := by
  cases e : FTy.tstep A with
  | none => rfl
  | some A' =>
      have h' : (match FTy.tstep A with
        | some A' => some (FTy.arr A' B)
        | none => (FTy.tstep B).map (FTy.arr A)) = none := h
      rw [e] at h'; cases h'

/-- With enough fuel the ladder normalizes an embedded type to `tnf F₀`. -/
theorem tnf_embT_stable {F₀ fuel : Nat} (hF : F₀ ≤ fuel) {A : FTy}
    (hA : FTy.tstep (FTy.tnf F₀ A) = none) : tnf fuel (embT A : FL.Ty α) = embT (FTy.tnf F₀ A) := by
  rw [tnf_embT, show fuel = F₀ + (fuel - F₀) by omega]
  rw [tnf_stable F₀ rfl hA (fuel - F₀)]

omit [DecidableEq α] [AtomOrder α] in
theorem map_ren_embT (Γ : List FTy) (G : List (FL.Ty α)) :
    (Γ.map embT ++ G).map (Ty.tren Nat.succ) =
      (Γ.map (FTy.ren Nat.succ)).map embT ++ G.map (Ty.tren Nat.succ) := by
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro A _
  exact (embT_ren A Nat.succ).symm

/-- **Soundness of `checkW`**, for the ladder's checker at every fuel `≥ F₀`. -/
theorem checkW_sound (F₀ : Nat) : ∀ (t : FTm) {Δ : List FK} {Γ : List FTy} {T : FTy},
    checkW F₀ Δ Γ t = some T → ∀ {fuel : Nat}, F₀ ≤ fuel →
    ∀ (D : List (Kind α)) (G : List (FL.Ty α)),
    infer fuel (Δ.map embK ++ D) (Γ.map embT ++ G) (embC t) = some (embT T)
  | .var n, Δ, Γ, T, h, fuel, _, D, G => by
      show nth? (Γ.map embT ++ G) n = _
      exact nth?_append_left (nth?_map_some embT h)
  | .lam A b, Δ, Γ, T, h, fuel, hF, D, G => by
      simp only [checkW] at h
      split at h
      · next hA =>
          cases hb : checkW F₀ Δ (A :: Γ) b with
          | none => rw [hb] at h; cases h
          | some B =>
              rw [hb] at h
              cases h
              exact Emb.infer_lam (kind_embT A D hA) (checkW_sound F₀ b hb hF D G)
      · cases h
  | .app t u, Δ, Γ, T, h, fuel, hF, D, G => by
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
                      show (match infer fuel (Δ.map embK ++ D) (Γ.map embT ++ G) (embC t),
                          infer fuel (Δ.map embK ++ D) (Γ.map embT ++ G) (embC u) with
                        | some T, some U => appResult fuel T U
                        | _, _ => none) = _
                      rw [checkW_sound F₀ t ht hF D G, checkW_sound F₀ u hu hF D G]
                      show (match tnf fuel (embT T₁ : FL.Ty α) with
                        | FL.Ty.arr A B => if tnf fuel A = tnf fuel (embT U) then some B else none
                        | _ => none) = _
                      rw [tnf_embT_stable hF (hT ▸ hs1), hT,
                        tnf_embT_stable hF hs2, ← hAU]
                      have hsA : tstep (embT A : FL.Ty α) = none := by
                        rw [tstep_embT, tstep_arr_left hs1]; rfl
                      show (if tnf fuel (embT A : FL.Ty α) = embT A then some _ else none) = _
                      rw [Emb.tnf_eq hsA]
                      simp only [↓reduceIte]
                  · cases h
              | tvar _ => simp only [checkW, ht, hu, hT] at h; cases h
              | all _ _ => simp only [checkW, ht, hu, hT] at h; cases h
              | lam _ _ => simp only [checkW, ht, hu, hT] at h; cases h
              | app _ _ _ => simp only [checkW, ht, hu, hT] at h; cases h
  | .tlam k b, Δ, Γ, T, h, fuel, hF, D, G => by
      simp only [checkW] at h
      cases hb : checkW F₀ (k :: Δ) (Γ.map (FTy.ren Nat.succ)) b with
      | none => rw [hb] at h; cases h
      | some B =>
          rw [hb] at h
          cases h
          have ih := checkW_sound F₀ b hb hF D (G.map (Ty.tren Nat.succ))
          rw [← map_ren_embT] at ih
          show (infer fuel (embK k :: (Δ.map embK ++ D))
            ((Γ.map embT ++ G).map (Ty.tren Nat.succ)) (embC b)).map (FL.Ty.all (embK k)) = _
          rw [show embK k :: (Δ.map embK ++ D) = (k :: Δ).map embK ++ D from rfl, ih]
          rfl
  | .tapp t B, Δ, Γ, T, h, fuel, hF, D, G => by
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
                  show (match infer fuel (Δ.map embK ++ D) (Γ.map embT ++ G) (embC t) with
                    | some T => tappResult fuel (Δ.map embK ++ D) T (embT B)
                    | none => none) = _
                  rw [checkW_sound F₀ t ht hF D G]
                  show (match tnf fuel (embT T₁ : FL.Ty α) with
                    | FL.Ty.all k A => if inferKind (Δ.map embK ++ D) (embT B) = some k
                        then some (Ty.inst A (embT B)) else none
                    | _ => none) = _
                  rw [tnf_embT_stable hF (hT ▸ hs1), hT]
                  show (if inferKind (Δ.map embK ++ D) (embT B) = some (embK k)
                    then some (Ty.inst (embT A) (embT B)) else none) = _
                  rw [kind_embT B D hc.2, embT_inst]
                  simp only [↓reduceIte]
              · cases h
          | tvar _ => simp only [checkW, ht, hT] at h; cases h
          | arr _ _ => simp only [checkW, ht, hT] at h; cases h
          | lam _ _ => simp only [checkW, ht, hT] at h; cases h
          | app _ _ _ => simp only [checkW, ht, hT] at h; cases h

/-- A closed program accepted by `checkW F₀` is accepted by the ladder in every context,
at every fuel `≥ F₀`. -/
theorem infer_embC {F₀ : Nat} {t : FTm} {T : FTy} (h : checkW F₀ [] [] t = some T)
    {fuel : Nat} (hF : F₀ ≤ fuel) (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ (embC t) = some (embT T) :=
  checkW_sound F₀ t h hF Δ Γ

end BusyLean.Indep.FW
