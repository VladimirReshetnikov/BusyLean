import BusyLean.SystemFd.Typing
import BusyLean.SystemFw.Candidates

/-!
# Strong normalization of dynamic-kind System Fω (with oracle)

Semantic kinds are closed syntactic kinds. The domain of `dyn` is Fω's `SVal`,
i.e. `Σ k, Sem k` over closed *dyn-free* kinds: a predicative universe that
does not contain itself. `pack` is `SVal.mk` and `unpack` is the dynamic read
`SVal.get`, both through a cast along `toFw`, which decodes a dyn-free closed
kind as an Fω kind. The conversion `unpack K (pack K A) ⟶ A` is preserved
because the read-back of a packed value is the value itself.

Level-0 kind variables are evaluated to closed Fω kinds (`θ₀`), and level-1
variables to arbitrary kinds (`θ₁`). `∀κ₀` is the intersection over Fω kinds,
and `∀κ₁` the intersection over all kinds.
-/

namespace BusyLean.Fd

open BusyLean.F (Tm Cand snCand arrCand Step SN)
open Ty

variable {f : Nat → Nat}

/-- Semantic domains of (closed) kinds. Variables never occur in closed kinds;
they get a junk domain. -/
def Sem (f : Nat → Nat) : Kind → Type
  | .star => Cand f
  | .arr a b => Sem f a → Sem f b
  | .dyn => Fw.SVal f
  | .kvar _ => Cand f
  | .dvar _ => Cand f

def dflt (f : Nat → Nat) : (k : Kind) → Sem f k
  | .star => snCand f
  | .arr _ b => fun _ => dflt f b
  | .dyn => ⟨.star, snCand f⟩
  | .kvar _ => snCand f
  | .dvar _ => snCand f

structure SVal (f : Nat → Nat) where
  kind : Kind
  val : Sem f kind

def SVal.get (x : SVal f) (k : Kind) : Sem f k :=
  if h : x.kind = k then h ▸ x.val else dflt f k

theorem SVal.get_self (k : Kind) (v : Sem f k) : (SVal.mk k v).get k = v := by
  unfold SVal.get
  rw [dite_eq_left rfl]

theorem SVal.eta {x : SVal f} {k : Kind} (h : x.kind = k) : SVal.mk k (x.get k) = x := by
  obtain ⟨k', v⟩ := x
  cases h
  rw [SVal.get_self]

def scons (x : SVal f) (ρ : Nat → SVal f) : Nat → SVal f
  | 0 => x
  | n + 1 => ρ n

/-! ## Dyn-free kinds as Fω kinds -/

def emb : Fw.Kind → Kind
  | .star => .star
  | .arr a b => .arr (emb a) (emb b)

def toFw : Kind → Option Fw.Kind
  | .star => some .star
  | .arr a b =>
      match toFw a, toFw b with
      | some a', some b' => some (.arr a' b')
      | _, _ => none
  | .kvar _ => none
  | .dvar _ => none
  | .dyn => none

theorem sem_toFw : ∀ {K : Kind} {k : Fw.Kind}, toFw K = some k → Sem f K = Fw.Sem f k
  | .star, k, h => by cases h; rfl
  | .arr a b, k, h => by
      simp only [toFw] at h
      cases ha : toFw a with
      | none => rw [ha] at h; cases h
      | some a' =>
          cases hb : toFw b with
          | none => rw [ha, hb] at h; cases h
          | some b' =>
              rw [ha, hb] at h
              cases h
              show (Sem f a → Sem f b) = (Fw.Sem f a' → Fw.Sem f b')
              rw [sem_toFw ha, sem_toFw hb]
  | .kvar _, _, h => nomatch h
  | .dvar _, _, h => nomatch h
  | .dyn, _, h => nomatch h

theorem toFw_emb : ∀ k : Fw.Kind, toFw (emb k) = some k
  | .star => rfl
  | .arr a b => by simp only [emb, toFw, toFw_emb a, toFw_emb b]

/-- Evaluate a kind under level-0 and level-1 valuations. -/
abbrev eval (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (K : Kind) : Kind :=
  K.subst (fun n => emb (θ₀ n)) θ₁

/-- A dyn-free kind evaluates to an Fω kind. -/
def evalFw (θ₀ : Nat → Fw.Kind) : Kind → Fw.Kind
  | .star => .star
  | .arr a b => .arr (evalFw θ₀ a) (evalFw θ₀ b)
  | .kvar n => θ₀ n
  | .dvar _ => .star
  | .dyn => .star

theorem eval_dynFree {θ₀ : Nat → Fw.Kind} {θ₁ : Nat → Kind} :
    ∀ {K : Kind}, K.DynFree → eval θ₀ θ₁ K = emb (evalFw θ₀ K)
  | .star, _ => rfl
  | .arr a b, h => by
      show Kind.arr (eval θ₀ θ₁ a) (eval θ₀ θ₁ b) = _
      rw [eval_dynFree h.1, eval_dynFree h.2]
      rfl
  | .kvar _, _ => rfl
  | .dvar _, h => h.elim
  | .dyn, h => h.elim

def θcons₀ (k : Fw.Kind) (θ : Nat → Fw.Kind) : Nat → Fw.Kind
  | 0 => k
  | n + 1 => θ n

/-! ## Interpretation -/

/-- Intersection over an inhabited type of parameters. -/
def allT (T : Type) (d : T) (F : T → Cand f) : Cand f where
  P t := ∀ X, (F X).P t
  cr1 h := (F d).cr1 (h _)
  cr2 h s X := (F X).cr2 (h X) s
  cr3 ht h X := (F X).cr3 ht fun u s => h u s X

/-- A candidate, placed at an expected kind (default unless the kind is `★`). -/
def onStar (k : Kind) (c : Cand f) : Sem f k :=
  match k with
  | .star => c
  | k => dflt f k

def packVal (K : Kind) (v : Sem f K) : Fw.SVal f :=
  match h : toFw K with
  | some k => ⟨k, cast (sem_toFw h) v⟩
  | none => ⟨.star, snCand f⟩

def unpackVal (k : Kind) (d : Fw.SVal f) : Sem f k :=
  match h : toFw k with
  | some k' => cast (sem_toFw h).symm (d.get k')
  | none => dflt f k

theorem unpack_pack {K : Kind} {k : Fw.Kind} (h : toFw K = some k) (v : Sem f K) :
    unpackVal K (packVal K v) = v := by
  unfold unpackVal packVal
  split
  · next k' h' =>
      split
      · next k'' h'' =>
          cases h''
          rw [Fw.SVal.get_self]
          simp
      · next h'' => cases h''
  · next h' => rw [h] at h'; cases h'

def interp (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f) :
    Ty → (k : Kind) → Sem f k
  | tvar n, k => (ρ n).get k
  | arr A B, k => onStar k (arrCand (interp θ₀ θ₁ ρ A .star) (interp θ₀ θ₁ ρ B .star))
  | all K A, k =>
      onStar k (allT (Sem f (eval θ₀ θ₁ K)) (dflt f _)
        fun X => interp θ₀ θ₁ (scons ⟨eval θ₀ θ₁ K, X⟩ ρ) A .star)
  | lam _ A, k =>
      match k with
      | .arr k₁ k₂ => fun X => interp θ₀ θ₁ (scons ⟨k₁, X⟩ ρ) A k₂
      | k => dflt f k
  | app K A B, k => interp θ₀ θ₁ ρ A (.arr (eval θ₀ θ₁ K) k) (interp θ₀ θ₁ ρ B (eval θ₀ θ₁ K))
  | kall0 A, k => onStar k (allT Fw.Kind .star fun k₀ => interp (θcons₀ k₀ θ₀) θ₁ ρ A .star)
  | kall1 A, k => onStar k (allT Kind .star fun K => interp θ₀ (Kind.kcons K θ₁) ρ A .star)
  | pack K A, k =>
      match k with
      | .dyn => packVal (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ A (eval θ₀ θ₁ K))
      | k => dflt f k
  | unpack _ X, k => unpackVal k (interp θ₀ θ₁ ρ X .dyn)

def WK (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (Δ : KCtx) (ρ : Nat → SVal f) : Prop :=
  ∀ n, (ρ n).kind = eval θ₀ θ₁ (Δ n)

theorem WK.cons {θ₀ : Nat → Fw.Kind} {θ₁ : Nat → Kind} {Δ : KCtx} {ρ : Nat → SVal f}
    (h : WK θ₀ θ₁ Δ ρ) (k : Kind) (X : Sem f (eval θ₀ θ₁ k)) :
    WK θ₀ θ₁ (kcons k Δ) (scons ⟨eval θ₀ θ₁ k, X⟩ ρ) := fun n => by
  cases n with
  | zero => rfl
  | succ n => exact h n

theorem eval_sh₀ (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (k₀ : Fw.Kind) (K : Kind) :
    eval (θcons₀ k₀ θ₀) θ₁ K.sh₀ = eval θ₀ θ₁ K := by
  unfold eval Kind.sh₀
  rw [Kind.subst_ren]
  rfl

theorem eval_sh₁ (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (K' K : Kind) :
    eval θ₀ (Kind.kcons K' θ₁) K.sh₁ = eval θ₀ θ₁ K := by
  unfold eval Kind.sh₁
  rw [Kind.subst_ren]
  rfl

theorem WK.klift0 {θ₀ : Nat → Fw.Kind} {θ₁ : Nat → Kind} {Δ : KCtx} {ρ : Nat → SVal f}
    (h : WK θ₀ θ₁ Δ ρ) (k₀ : Fw.Kind) : WK (θcons₀ k₀ θ₀) θ₁ Δ.klift0 ρ := fun n => by
  rw [h n]
  exact (eval_sh₀ θ₀ θ₁ k₀ (Δ n)).symm

theorem WK.klift1 {θ₀ : Nat → Fw.Kind} {θ₁ : Nat → Kind} {Δ : KCtx} {ρ : Nat → SVal f}
    (h : WK θ₀ θ₁ Δ ρ) (K : Kind) : WK θ₀ (Kind.kcons K θ₁) Δ.klift1 ρ := fun n => by
  rw [h n]
  exact (eval_sh₁ θ₀ θ₁ K (Δ n)).symm

/-! ## Renaming and substitution -/

theorem interp_tren : ∀ (A : Ty) (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f)
    (ξ : Nat → Nat) (k : Kind), interp θ₀ θ₁ ρ (tren ξ A) k = interp θ₀ θ₁ (ρ ∘ ξ) A k
  | tvar _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, ρ, ξ, k => by
      show onStar k _ = onStar k _
      rw [interp_tren A, interp_tren B]
  | all K A, θ₀, θ₁, ρ, ξ, k => by
      show onStar k _ = onStar k _
      congr 2; funext X
      rw [interp_tren A]
      congr 1; funext n; cases n <;> rfl
  | lam K A, θ₀, θ₁, ρ, ξ, k => by
      cases k with
      | arr k₁ k₂ =>
          funext X
          show interp θ₀ θ₁ _ (tren _ A) k₂ = interp θ₀ θ₁ _ A k₂
          rw [interp_tren A]
          congr 1; funext n; cases n <;> rfl
      | star => rfl
      | kvar _ => rfl
      | dvar _ => rfl
      | dyn => rfl
  | app K A B, θ₀, θ₁, ρ, ξ, k => by
      show interp θ₀ θ₁ ρ (tren ξ A) (.arr (eval θ₀ θ₁ K) k)
          (interp θ₀ θ₁ ρ (tren ξ B) (eval θ₀ θ₁ K)) = _
      rw [interp_tren A, interp_tren B]
      rfl
  | kall0 A, θ₀, θ₁, ρ, ξ, k => by
      show onStar k _ = onStar k _
      congr 2; funext k₀
      exact interp_tren A _ _ ρ ξ _
  | kall1 A, θ₀, θ₁, ρ, ξ, k => by
      show onStar k _ = onStar k _
      congr 2; funext K
      exact interp_tren A _ _ ρ ξ _
  | pack K A, θ₀, θ₁, ρ, ξ, k => by
      cases k with
      | dyn =>
          show packVal _ (interp θ₀ θ₁ ρ (tren ξ A) _) = packVal _ (interp θ₀ θ₁ _ A _)
          rw [interp_tren A]
      | star => rfl
      | arr _ _ => rfl
      | kvar _ => rfl
      | dvar _ => rfl
  | unpack K A, θ₀, θ₁, ρ, ξ, k => by
      show unpackVal k (interp θ₀ θ₁ ρ (tren ξ A) .dyn) = unpackVal k (interp θ₀ θ₁ _ A .dyn)
      rw [interp_tren A]

theorem eval_ren (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ξ₀ ξ₁ : Nat → Nat) (K : Kind) :
    eval θ₀ θ₁ (K.ren ξ₀ ξ₁) = eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) K := by
  unfold eval
  rw [Kind.subst_ren]
  rfl

theorem interp_kren : ∀ (A : Ty) (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f)
    (ξ₀ ξ₁ : Nat → Nat) (k : Kind),
    interp θ₀ θ₁ ρ (Ty.kren ξ₀ ξ₁ A) k = interp (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) ρ A k
  | tvar _, _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show onStar k _ = onStar k _
      rw [interp_kren A, interp_kren B]
  | all K A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show onStar k (allT (Sem f (eval θ₀ θ₁ (K.ren ξ₀ ξ₁))) _ _) =
        onStar k (allT (Sem f (eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) K)) _ _)
      rw [eval_ren]
      congr 2; funext X
      rw [interp_kren A]
  | lam K A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      cases k with
      | arr k₁ k₂ => funext X; exact interp_kren A θ₀ θ₁ _ ξ₀ ξ₁ k₂
      | star => rfl
      | kvar _ => rfl
      | dvar _ => rfl
      | dyn => rfl
  | app K A B, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show interp θ₀ θ₁ ρ (Ty.kren ξ₀ ξ₁ A) (.arr (eval θ₀ θ₁ (K.ren ξ₀ ξ₁)) k)
          (interp θ₀ θ₁ ρ (Ty.kren ξ₀ ξ₁ B) (eval θ₀ θ₁ (K.ren ξ₀ ξ₁))) = _
      rw [interp_kren A, interp_kren B, eval_ren]
      rfl
  | kall0 A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show onStar k _ = onStar k _
      congr 2; funext k₀
      rw [interp_kren A]
      congr 1; funext n; cases n <;> rfl
  | kall1 A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show onStar k _ = onStar k _
      congr 2; funext K
      rw [interp_kren A]
      congr 1; funext n; cases n <;> rfl
  | pack K A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      cases k with
      | dyn =>
          show packVal (eval θ₀ θ₁ (K.ren ξ₀ ξ₁))
              (interp θ₀ θ₁ ρ (Ty.kren ξ₀ ξ₁ A) (eval θ₀ θ₁ (K.ren ξ₀ ξ₁))) =
            packVal (eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) K) (interp _ _ ρ A (eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) K))
          rw [interp_kren A, eval_ren]
      | star => rfl
      | arr _ _ => rfl
      | kvar _ => rfl
      | dvar _ => rfl
  | unpack K A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show unpackVal k (interp θ₀ θ₁ ρ (Ty.kren ξ₀ ξ₁ A) .dyn) = _
      rw [interp_kren A]
      rfl

theorem eval_subst (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) {σ₀ σ₁ : Nat → Kind}
    (hσ : ∀ n, (σ₀ n).DynFree) (K : Kind) :
    eval θ₀ θ₁ (K.subst σ₀ σ₁) =
      eval (fun n => evalFw θ₀ (σ₀ n)) (fun n => eval θ₀ θ₁ (σ₁ n)) K := by
  unfold eval
  rw [Kind.subst_subst]
  congr 1
  funext n
  show eval θ₀ θ₁ (σ₀ n) = emb (evalFw θ₀ (σ₀ n))
  exact eval_dynFree (hσ n)

theorem interp_ksubst : ∀ (A : Ty) (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f)
    (σ₀ σ₁ : Nat → Kind) (_ : ∀ n, (σ₀ n).DynFree) (k : Kind),
    interp θ₀ θ₁ ρ (Ty.ksubst σ₀ σ₁ A) k =
      interp (fun n => evalFw θ₀ (σ₀ n)) (fun n => eval θ₀ θ₁ (σ₁ n)) ρ A k
  | tvar _, _, _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show onStar k _ = onStar k _
      rw [interp_ksubst A _ _ _ _ _ hσ, interp_ksubst B _ _ _ _ _ hσ]
  | all K A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show onStar k (allT (Sem f (eval θ₀ θ₁ (K.subst σ₀ σ₁))) _ _) = onStar k (allT _ _ _)
      rw [eval_subst θ₀ θ₁ hσ]
      congr 2; funext X
      rw [interp_ksubst A _ _ _ _ _ hσ]
  | lam K A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      cases k with
      | arr k₁ k₂ => funext X; exact interp_ksubst A θ₀ θ₁ _ σ₀ σ₁ hσ k₂
      | star => rfl
      | kvar _ => rfl
      | dvar _ => rfl
      | dyn => rfl
  | app K A B, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show interp θ₀ θ₁ ρ (Ty.ksubst σ₀ σ₁ A) (.arr (eval θ₀ θ₁ (K.subst σ₀ σ₁)) k)
          (interp θ₀ θ₁ ρ (Ty.ksubst σ₀ σ₁ B) (eval θ₀ θ₁ (K.subst σ₀ σ₁))) = _
      rw [interp_ksubst A _ _ _ _ _ hσ, interp_ksubst B _ _ _ _ _ hσ, eval_subst θ₀ θ₁ hσ]
      rfl
  | kall0 A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show onStar k _ = onStar k _
      congr 2; funext k₀
      have hσ' : ∀ n, ((kup₀ σ₀ σ₁).1 n).DynFree := fun n => by
        cases n with
        | zero => trivial
        | succ n => exact (hσ n).ren _ _
      rw [interp_ksubst A _ _ _ _ _ hσ']
      congr 1
      · funext n
        cases n with
        | zero => rfl
        | succ n =>
            show evalFw (θcons₀ k₀ θ₀) ((σ₀ n).ren Nat.succ id) = evalFw θ₀ (σ₀ n)
            have h1 := eval_sh₀ θ₀ θ₁ k₀ (σ₀ n)
            rw [eval_dynFree (K := (σ₀ n).sh₀) ((hσ n).ren _ _), eval_dynFree (hσ n)] at h1
            exact emb_inj h1
      · funext n
        exact eval_sh₀ θ₀ θ₁ k₀ (σ₁ n)
  | kall1 A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show onStar k _ = onStar k _
      congr 2; funext K
      have hσ' : ∀ n, ((kup₁ σ₀ σ₁).1 n).DynFree := fun n => (hσ n).ren _ _
      rw [interp_ksubst A _ _ _ _ _ hσ']
      congr 1
      · funext n
        show evalFw θ₀ ((σ₀ n).ren id Nat.succ) = evalFw θ₀ (σ₀ n)
        have h1 := eval_sh₁ θ₀ θ₁ K (σ₀ n)
        rw [eval_dynFree (K := (σ₀ n).sh₁) ((hσ n).ren _ _), eval_dynFree (hσ n)] at h1
        exact emb_inj h1
      · funext n
        cases n with
        | zero => rfl
        | succ n => exact eval_sh₁ θ₀ θ₁ K (σ₁ n)
  | pack K A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      cases k with
      | dyn =>
          show packVal (eval θ₀ θ₁ (K.subst σ₀ σ₁))
              (interp θ₀ θ₁ ρ (Ty.ksubst σ₀ σ₁ A) (eval θ₀ θ₁ (K.subst σ₀ σ₁))) = _
          rw [interp_ksubst A _ _ _ _ _ hσ, eval_subst θ₀ θ₁ hσ]
          rfl
      | star => rfl
      | arr _ _ => rfl
      | kvar _ => rfl
      | dvar _ => rfl
  | unpack K A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show unpackVal k (interp θ₀ θ₁ ρ (Ty.ksubst σ₀ σ₁ A) .dyn) = _
      rw [interp_ksubst A _ _ _ _ _ hσ]
      rfl
where
  emb_inj : ∀ {a b : Fw.Kind}, emb a = emb b → a = b := fun {a b} h => by
    have := congrArg toFw h
    rw [toFw_emb, toFw_emb] at this
    exact Option.some.inj this

theorem interp_subst {Δ : KCtx} {A : Ty} {k : Kind} (h : Kinded Δ A k) :
    ∀ (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f) (σ : Nat → Ty),
      interp θ₀ θ₁ ρ (tsubst σ A) (eval θ₀ θ₁ k) =
        interp θ₀ θ₁ (fun n => ⟨eval θ₀ θ₁ (Δ n), interp θ₀ θ₁ ρ (σ n) (eval θ₀ θ₁ (Δ n))⟩) A
          (eval θ₀ θ₁ k) := by
  induction h with
  | tvar n =>
      intro θ₀ θ₁ ρ σ
      show interp θ₀ θ₁ ρ (σ n) _ = SVal.get ⟨_, interp θ₀ θ₁ ρ (σ n) _⟩ _
      rw [SVal.get_self]
  | arr _ _ ih₁ ih₂ =>
      intro θ₀ θ₁ ρ σ
      show onStar _ (arrCand _ _) = onStar _ (arrCand _ _)
      exact (congrArg (fun a => onStar _ (arrCand a _)) (ih₁ θ₀ θ₁ ρ σ)).trans
        (congrArg (fun b => onStar _ (arrCand _ b)) (ih₂ θ₀ θ₁ ρ σ))
  | @all Δ K A _ ih =>
      intro θ₀ θ₁ ρ σ
      show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
      congr 2; funext X
      have := ih θ₀ θ₁ (scons ⟨eval θ₀ θ₁ K, X⟩ ρ) (tup σ)
      refine this.trans ?_
      congr 1; funext n
      cases n with
      | zero =>
          exact congrArg (SVal.mk _) (SVal.get_self _ X)
      | succ n =>
          show SVal.mk (eval θ₀ θ₁ (Δ n))
              (interp θ₀ θ₁ (scons ⟨eval θ₀ θ₁ K, X⟩ ρ) (tren Nat.succ (σ n))
                (eval θ₀ θ₁ (Δ n))) = _
          rw [interp_tren]
          rfl
  | @lam Δ k₁ k₂ A _ ih =>
      intro θ₀ θ₁ ρ σ
      funext X
      have := ih θ₀ θ₁ (scons ⟨eval θ₀ θ₁ k₁, X⟩ ρ) (tup σ)
      refine this.trans ?_
      congr 1; funext n
      cases n with
      | zero =>
          exact congrArg (SVal.mk _) (SVal.get_self _ X)
      | succ n =>
          show SVal.mk (eval θ₀ θ₁ (Δ n))
              (interp θ₀ θ₁ (scons ⟨eval θ₀ θ₁ k₁, X⟩ ρ) (tren Nat.succ (σ n))
                (eval θ₀ θ₁ (Δ n))) = _
          rw [interp_tren]
          rfl
  | @app Δ k₁ k₂ A B _ _ ih₁ ih₂ =>
      intro θ₀ θ₁ ρ σ
      show interp θ₀ θ₁ ρ (tsubst σ A) (.arr (eval θ₀ θ₁ k₁) (eval θ₀ θ₁ k₂))
          (interp θ₀ θ₁ ρ (tsubst σ B) (eval θ₀ θ₁ k₁)) = _
      have h₁ := ih₁ θ₀ θ₁ ρ σ
      have h₂ := ih₂ θ₀ θ₁ ρ σ
      have e : eval θ₀ θ₁ (.arr k₁ k₂) = .arr (eval θ₀ θ₁ k₁) (eval θ₀ θ₁ k₂) := rfl
      rw [e] at h₁
      rw [h₁, h₂]
      rfl
  | @kall0 Δ A _ ih =>
      intro θ₀ θ₁ ρ σ
      show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
      congr 2; funext k₀
      have := ih (θcons₀ k₀ θ₀) θ₁ ρ (fun n => Ty.kren Nat.succ id (σ n))
      refine this.trans ?_
      congr 1; funext n
      show SVal.mk (eval (θcons₀ k₀ θ₀) θ₁ (Δ n).sh₀)
          (interp (θcons₀ k₀ θ₀) θ₁ ρ (Ty.kren Nat.succ id (σ n))
            (eval (θcons₀ k₀ θ₀) θ₁ (Δ n).sh₀)) = _
      rw [eval_sh₀, interp_kren]
      rfl
  | @kall1 Δ A _ ih =>
      intro θ₀ θ₁ ρ σ
      show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
      congr 2; funext K
      have := ih θ₀ (Kind.kcons K θ₁) ρ (fun n => Ty.kren id Nat.succ (σ n))
      refine this.trans ?_
      congr 1; funext n
      show SVal.mk (eval θ₀ (Kind.kcons K θ₁) (Δ n).sh₁)
          (interp θ₀ (Kind.kcons K θ₁) ρ (Ty.kren id Nat.succ (σ n))
            (eval θ₀ (Kind.kcons K θ₁) (Δ n).sh₁)) = _
      rw [eval_sh₁, interp_kren]
      rfl
  | @pack Δ K A _ _ ih =>
      intro θ₀ θ₁ ρ σ
      show packVal (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ (tsubst σ A) (eval θ₀ θ₁ K)) =
        packVal (eval θ₀ θ₁ K) (interp θ₀ θ₁ _ A (eval θ₀ θ₁ K))
      rw [ih θ₀ θ₁ ρ σ]
  | @unpack Δ K A _ _ ih =>
      intro θ₀ θ₁ ρ σ
      show unpackVal _ (interp θ₀ θ₁ ρ (tsubst σ A) .dyn) = unpackVal _ (interp θ₀ θ₁ _ A .dyn)
      exact congrArg (unpackVal _) (ih θ₀ θ₁ ρ σ)

theorem interp_inst {θ₀ : Nat → Fw.Kind} {θ₁ : Nat → Kind} {Δ : KCtx} {k k' : Kind} {A : Ty}
    (B : Ty) (hA : Kinded (kcons k Δ) A k') {ρ : Nat → SVal f} (hρ : WK θ₀ θ₁ Δ ρ) :
    interp θ₀ θ₁ ρ (Ty.inst A B) (eval θ₀ θ₁ k') =
      interp θ₀ θ₁ (scons ⟨eval θ₀ θ₁ k, interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k)⟩ ρ) A
        (eval θ₀ θ₁ k') := by
  unfold Ty.inst
  rw [interp_subst hA]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => exact SVal.eta (hρ n)

theorem interp_kinst0 (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f) (A : Ty)
    {K : Kind} (hK : K.DynFree) (k : Kind) :
    interp θ₀ θ₁ ρ (Ty.kinst0 A K) k = interp (θcons₀ (evalFw θ₀ K) θ₀) θ₁ ρ A k := by
  unfold Ty.kinst0
  rw [interp_ksubst A _ _ _ _ _ (fun n => by cases n with
    | zero => exact hK
    | succ n => trivial)]
  congr 1
  funext n
  cases n <;> rfl

theorem interp_kinst1 (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f) (A : Ty)
    (K : Kind) (k : Kind) :
    interp θ₀ θ₁ ρ (Ty.kinst1 A K) k = interp θ₀ (Kind.kcons (eval θ₀ θ₁ K) θ₁) ρ A k := by
  unfold Ty.kinst1
  rw [interp_ksubst A θ₀ θ₁ ρ Kind.kvar (Kind.kcons K Kind.dvar) (fun _ => trivial)]
  congr 1
  funext n
  cases n <;> rfl

/-! ## Conversion -/

theorem interp_step {Δ : KCtx} {A B : Ty} {k : Kind} (h : Kinded Δ A k) (s : TStep A B)
    {θ₀ : Nat → Fw.Kind} {θ₁ : Nat → Kind} {ρ : Nat → SVal f} (hρ : WK θ₀ θ₁ Δ ρ) :
    interp θ₀ θ₁ ρ A (eval θ₀ θ₁ k) = interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k) := by
  induction s generalizing Δ k θ₀ θ₁ ρ with
  | beta k₁ k' A B =>
      cases h with
      | app hA hB =>
          cases hA with
          | lam hA' =>
              show interp θ₀ θ₁ (scons ⟨eval θ₀ θ₁ k₁, interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k₁)⟩ ρ) A
                (eval θ₀ θ₁ k) = _
              rw [interp_inst B hA' hρ]
  | unpackPack K A hK =>
      cases h with
      | unpack hX _ =>
          cases hX with
          | pack hA _ =>
              show unpackVal (eval θ₀ θ₁ K)
                (packVal (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ A (eval θ₀ θ₁ K))) = _
              have e : toFw (eval θ₀ θ₁ K) = some (evalFw θ₀ K) := by
                rw [eval_dynFree hK, toFw_emb]
              exact unpack_pack e _
  | arrL _ _ ih =>
      cases h with
      | arr h₁ _ =>
          have e := ih h₁ hρ
          show onStar _ (arrCand _ _) = onStar _ (arrCand _ _)
          exact congrArg (fun c => onStar _ (arrCand c _)) e
  | arrR _ _ ih =>
      cases h with
      | arr _ h₂ =>
          have e := ih h₂ hρ
          show onStar _ (arrCand _ _) = onStar _ (arrCand _ _)
          exact congrArg (fun c => onStar _ (arrCand _ c)) e
  | all K _ ih =>
      cases h with
      | all h₁ =>
          show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
          congr 2; funext X
          exact ih h₁ (hρ.cons K X)
  | lam K _ ih =>
      cases h with
      | lam h₁ => funext X; exact ih h₁ (hρ.cons K X)
  | @appL k' A A' B _ ih =>
      cases h with
      | app h₁ _ =>
          show interp θ₀ θ₁ ρ A (.arr (eval θ₀ θ₁ k') (eval θ₀ θ₁ k))
              (interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k')) =
            interp θ₀ θ₁ ρ A' (.arr (eval θ₀ θ₁ k') (eval θ₀ θ₁ k))
              (interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k'))
          have := ih h₁ hρ
          have e : eval θ₀ θ₁ (.arr k' k) = .arr (eval θ₀ θ₁ k') (eval θ₀ θ₁ k) := rfl
          rw [e] at this
          rw [this]
  | @appR k' A B B' _ ih =>
      cases h with
      | app _ h₂ =>
          show interp θ₀ θ₁ ρ A (.arr (eval θ₀ θ₁ k') (eval θ₀ θ₁ k))
              (interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k')) =
            interp θ₀ θ₁ ρ A (.arr (eval θ₀ θ₁ k') (eval θ₀ θ₁ k))
              (interp θ₀ θ₁ ρ B' (eval θ₀ θ₁ k'))
          rw [ih h₂ hρ]
  | kall0 _ ih =>
      cases h with
      | kall0 h₁ =>
          show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
          congr 2; funext k₀
          exact ih h₁ (hρ.klift0 k₀)
  | kall1 _ ih =>
      cases h with
      | kall1 h₁ =>
          show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
          congr 2; funext K
          exact ih h₁ (hρ.klift1 K)
  | @pack K A A' _ ih =>
      cases h with
      | pack h₁ _ =>
          show packVal (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ A (eval θ₀ θ₁ K)) =
            packVal (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ A' (eval θ₀ θ₁ K))
          rw [ih h₁ hρ]
  | @unpack K A A' _ ih =>
      cases h with
      | unpack h₁ _ =>
          show unpackVal _ (interp θ₀ θ₁ ρ A .dyn) = unpackVal _ (interp θ₀ θ₁ ρ A' .dyn)
          have := ih h₁ hρ
          exact congrArg (unpackVal _) this

theorem interp_steps {Δ : KCtx} {A B : Ty} {k : Kind} (h : Kinded Δ A k) (s : TSteps A B)
    {θ₀ : Nat → Fw.Kind} {θ₁ : Nat → Kind} {ρ : Nat → SVal f} (hρ : WK θ₀ θ₁ Δ ρ) :
    interp θ₀ θ₁ ρ A (eval θ₀ θ₁ k) = interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k) := by
  induction s with
  | refl => rfl
  | step s _ ih => exact (interp_step h s hρ).trans (ih (h.step s))

theorem interp_join {Δ : KCtx} {A B : Ty} {k : Kind} (hA : Kinded Δ A k) (hB : Kinded Δ B k)
    (j : TJoin A B) {θ₀ : Nat → Fw.Kind} {θ₁ : Nat → Kind} {ρ : Nat → SVal f}
    (hρ : WK θ₀ θ₁ Δ ρ) : interp θ₀ θ₁ ρ A (eval θ₀ θ₁ k) = interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k) := by
  obtain ⟨C, sA, sB⟩ := j
  exact (interp_steps hA sA hρ).trans (interp_steps hB sB hρ).symm

/-! ## Adequacy and strong normalization -/

def OrcOK (f : Nat → Nat) : Prop :=
  ∀ (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f),
    (interp θ₀ θ₁ ρ (arr Ty.nat Ty.nat) .star).P Tm.orc

theorem adequacy {o : Bool} {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed o Δ Γ t A)
    (ho : o = true → OrcOK f) :
    ∀ (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f), WK θ₀ θ₁ Δ ρ →
      ∀ (σ : Nat → Tm), (∀ n, (interp θ₀ θ₁ ρ (Γ n) .star).P (σ n)) →
        (interp θ₀ θ₁ ρ A .star).P (Tm.subst σ t) := by
  induction ht with
  | var n => intro θ₀ θ₁ ρ _ σ h; exact h n
  | lam _ ih =>
      intro θ₀ θ₁ ρ hρ σ h
      refine F.lam_mem fun a ha => ?_
      rw [Tm.subst_beta]
      exact ih θ₀ θ₁ ρ hρ (Tm.cons a σ) fun n => by
        cases n with
        | zero => exact ha
        | succ n => exact h n
  | app _ _ ih₁ ih₂ =>
      intro θ₀ θ₁ ρ hρ σ h; exact ih₁ θ₀ θ₁ ρ hρ σ h _ (ih₂ θ₀ θ₁ ρ hρ σ h)
  | @gen Δ Γ k A t _ ih =>
      intro θ₀ θ₁ ρ hρ σ h X
      refine ih θ₀ θ₁ (scons ⟨eval θ₀ θ₁ k, X⟩ ρ) (hρ.cons k X) σ fun n => ?_
      show (interp θ₀ θ₁ (scons ⟨eval θ₀ θ₁ k, X⟩ ρ) (tren Nat.succ (Γ n)) .star).P (σ n)
      rw [interp_tren]
      exact h n
  | @inst Δ Γ k A t B _ hA _ ih =>
      intro θ₀ θ₁ ρ hρ σ h
      have hall := ih θ₀ θ₁ ρ hρ σ h (interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k))
      have e := interp_inst (f := f) B hA hρ (k' := .star)
      show (interp θ₀ θ₁ ρ (Ty.inst A B) (eval θ₀ θ₁ .star)).P _
      rw [e]
      exact hall
  | conv _ hA hB j ih =>
      intro θ₀ θ₁ ρ hρ σ h
      have e := interp_join (f := f) hA hB j hρ
      show (interp θ₀ θ₁ ρ _ (eval θ₀ θ₁ .star)).P _
      rw [← e]
      exact ih θ₀ θ₁ ρ hρ σ h
  | @kgen0 Δ Γ A t _ ih =>
      intro θ₀ θ₁ ρ hρ σ h k₀
      refine ih (θcons₀ k₀ θ₀) θ₁ ρ (hρ.klift0 k₀) σ fun n => ?_
      show (interp (θcons₀ k₀ θ₀) θ₁ ρ (Ty.kren Nat.succ id (Γ n)) .star).P (σ n)
      rw [interp_kren]
      exact h n
  | @kinst0 Δ Γ A t K _ hK ih =>
      intro θ₀ θ₁ ρ hρ σ h
      rw [interp_kinst0 θ₀ θ₁ ρ A hK]
      exact ih θ₀ θ₁ ρ hρ σ h (evalFw θ₀ K)
  | @kgen1 Δ Γ A t _ ih =>
      intro θ₀ θ₁ ρ hρ σ h K
      refine ih θ₀ (Kind.kcons K θ₁) ρ (hρ.klift1 K) σ fun n => ?_
      show (interp θ₀ (Kind.kcons K θ₁) ρ (Ty.kren id Nat.succ (Γ n)) .star).P (σ n)
      rw [interp_kren]
      exact h n
  | @kinst1 Δ Γ A t K _ ih =>
      intro θ₀ θ₁ ρ hρ σ h
      rw [interp_kinst1]
      exact ih θ₀ θ₁ ρ hρ σ h (eval θ₀ θ₁ K)
  | orc e => intro θ₀ θ₁ ρ _ σ _; exact ho e θ₀ θ₁ ρ

theorem sn_of_typed' {o : Bool} {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty}
    (ht : Typed o Δ Γ t A) (ho : o = true → OrcOK f) : SN f t := by
  have h := adequacy ht ho (fun _ => .star) (fun _ => .star)
    (fun n => ⟨eval (fun _ => .star) (fun _ => .star) (Δ n), dflt f _⟩)
    (fun _ => rfl) Tm.var fun n => (interp _ _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact (interp _ _ _ A .star).cr1 h

theorem num_mem (θ₀ : Nat → Fw.Kind) (θ₁ : Nat → Kind) (ρ : Nat → SVal f) (n : Nat) :
    (interp θ₀ θ₁ ρ Ty.nat .star).P (Tm.num n) := by
  have h := adequacy (f := f)
    (typed_num false (fun _ => Kind.star) (fun _ => Ty.nat) n)
    (fun e => Bool.noConfusion e) θ₀ θ₁ (fun _ => ⟨eval θ₀ θ₁ .star, dflt f _⟩) (fun _ => rfl)
    Tm.var fun k => (interp θ₀ θ₁ _ Ty.nat .star).var k
  rw [Tm.subst_var] at h
  exact h

theorem orcOK (f : Nat → Nat) : OrcOK f := by
  intro θ₀ θ₁ ρ a ha
  have hsn := (interp θ₀ θ₁ ρ Ty.nat .star).cr1 ha
  revert ha
  induction hsn with
  | intro a _ ih =>
      intro ha
      refine (interp θ₀ θ₁ ρ Ty.nat .star).cr3 trivial fun v s => ?_
      cases s with
      | delta n => exact num_mem θ₀ θ₁ ρ (f n)
      | appL _ s => exact nomatch s
      | appR _ s => exact ih _ s ((interp θ₀ θ₁ ρ Ty.nat .star).cr2 ha s)

/-- **Strong normalization of dynamic-kind System Fω with oracle.** -/
theorem sn_of_typed {Δ : KCtx} {Γ : Ctx} {t : Tm} {A : Ty} (ht : Typed true Δ Γ t A) :
    SN f t :=
  sn_of_typed' ht fun _ => orcOK f

end BusyLean.Fd
