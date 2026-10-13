import BusyLean.SystemFL.Typing
import BusyLean.SystemF.Candidates

/-!
# Strong normalization of the ladder language (parametric in a universe)

The model of Contender 13, parametric in a `Universe`: a type `α` of atoms with
semantic domains `El a`, a packing map `pk` from base kinds that fit `a`, a
reading map `rd`, and the law `rd (pk v) = v`. *Base kinds* (`★`, `→`,
atoms) replace Fω's kinds. `dyn` is `Σ k : BaseKind α, Sem k`, level-0 kind
variables range over base kinds, `apack`/`aunpack` are `pk`/`rd`, and the
conversion `aunpack (apack A) ⟶ A` is preserved by the law.

Normalization holds for **every** universe, so the theorem is uniform in the
ladder level.
-/

namespace BusyLean.FL

open BusyLean.F (Tm Cand snCand arrCand Step SN)
open Ty

variable {f : Nat → Nat} {α : Type} [DecidableEq α] [AtomOrder α]

/-- Closed dyn-free kinds: the kinds whose operators live in `dyn`. -/
inductive BaseKind (α : Type) where
  | star : BaseKind α
  | arr : BaseKind α → BaseKind α → BaseKind α
  | atom : α → BaseKind α
  deriving DecidableEq

/-- Base kinds that fit the atom `a` (all their atoms are below `a`). -/
def BaseKind.Fits (a : α) : BaseKind α → Prop
  | .star => True
  | .arr x y => BaseKind.Fits a x ∧ BaseKind.Fits a y
  | .atom b => AtomOrder.lt b a = true

def BaseKind.fits (a : α) : BaseKind α → Bool
  | .star => true
  | .arr x y => BaseKind.fits a x && BaseKind.fits a y
  | .atom b => AtomOrder.lt b a

omit [DecidableEq α] in
theorem BaseKind.fits_iff (a : α) : ∀ k : BaseKind α, k.fits a = true ↔ k.Fits a
  | .star => by simp [BaseKind.fits, BaseKind.Fits]
  | .arr x y => by simp [BaseKind.fits, BaseKind.Fits, BaseKind.fits_iff a x, BaseKind.fits_iff a y]
  | .atom _ => by simp [BaseKind.fits, BaseKind.Fits]

/-- Semantic domains of base kinds, given the domains of the atoms. -/
def SemB (f : Nat → Nat) (El : α → Type) : BaseKind α → Type
  | .star => Cand f
  | .arr x y => SemB f El x → SemB f El y
  | .atom a => El a

/-- A universe of atoms: domains, packing, reading, and the read-back law. -/
structure Universe (f : Nat → Nat) (α : Type) [DecidableEq α] [AtomOrder α] where
  El : α → Type
  d : (a : α) → El a
  pk : (a : α) → (k : BaseKind α) → k.Fits a → SemB f El k → El a
  rd : (a : α) → (k : BaseKind α) → El a → SemB f El k
  rd_pk : ∀ a k h v, rd a k (pk a k h v) = v

def dfltB (U : Universe f α) : (k : BaseKind α) → SemB f U.El k
  | .star => snCand f
  | .arr _ y => fun _ => dfltB U y
  | .atom a => U.d a

/-- An operator of some base kind: the elements of `dyn`. -/
structure BVal (U : Universe f α) where
  kind : BaseKind α
  val : SemB f U.El kind

def BVal.get {U : Universe f α} (x : BVal U) (k : BaseKind α) : SemB f U.El k :=
  if h : x.kind = k then h ▸ x.val else dfltB U k

theorem BVal.get_self {U : Universe f α} (k : BaseKind α) (v : SemB f U.El k) :
    (BVal.mk k v).get k = v := by
  unfold BVal.get
  rw [dite_eq_left rfl]

variable {U : Universe f α}

/-- Semantic domains of (closed) kinds. Variables never occur in closed kinds;
they get a junk domain. -/
def Sem (U : Universe f α) : (Kind α) → Type
  | .star => Cand f
  | .arr a b => Sem U a → Sem U b
  | .dyn => BVal U
  | .atom a => U.El a
  | .kvar _ => Cand f
  | .dvar _ => Cand f

def dflt (U : Universe f α) : (k : (Kind α)) → Sem U k
  | .star => snCand f
  | .arr _ b => fun _ => dflt U b
  | .dyn => ⟨.star, snCand f⟩
  | .kvar _ => snCand f
  | .dvar _ => snCand f
  | .atom a => U.d a

structure SVal (U : Universe f α) where
  kind : (Kind α)
  val : Sem U kind

def SVal.get (x : SVal U) (k : (Kind α)) : Sem U k :=
  if h : x.kind = k then h ▸ x.val else dflt U k

theorem SVal.get_self (k : (Kind α)) (v : Sem U k) : (SVal.mk k v).get k = v := by
  unfold SVal.get
  rw [dite_eq_left rfl]

theorem SVal.eta {x : SVal U} {k : (Kind α)} (h : x.kind = k) : SVal.mk k (x.get k) = x := by
  obtain ⟨k', v⟩ := x
  cases h
  rw [SVal.get_self]

def scons (x : SVal U) (ρ : Nat → SVal U) : Nat → SVal U
  | 0 => x
  | n + 1 => ρ n

/-! ## Dyn-free kinds as Fω kinds -/

def emb : (BaseKind α) → (Kind α)
  | .star => .star
  | .arr a b => .arr (emb a) (emb b)
  | .atom a => .atom a

def toB : (Kind α) → Option (BaseKind α)
  | .star => some .star
  | .arr a b =>
      match toB a, toB b with
      | some a', some b' => some (.arr a' b')
      | _, _ => none
  | .kvar _ => none
  | .dvar _ => none
  | .dyn => none
  | .atom a => some (.atom a)

theorem sem_toB : ∀ {K : (Kind α)} {k : (BaseKind α)}, toB K = some k → Sem U K = SemB f U.El k
  | .star, k, h => by cases h; rfl
  | .arr a b, k, h => by
      simp only [toB] at h
      cases ha : toB a with
      | none => rw [ha] at h; cases h
      | some a' =>
          cases hb : toB b with
          | none => rw [ha, hb] at h; cases h
          | some b' =>
              rw [ha, hb] at h
              cases h
              show (Sem U a → Sem U b) = (SemB f U.El a' → SemB f U.El b')
              rw [sem_toB ha, sem_toB hb]
  | .kvar _, _, h => nomatch h
  | .dvar _, _, h => nomatch h
  | .dyn, _, h => nomatch h
  | .atom _, k, h => by cases h; rfl

omit [DecidableEq α] [AtomOrder α] in
theorem toB_emb : ∀ k : (BaseKind α), toB (emb k) = some k
  | .star => rfl
  | .arr a b => by simp only [emb, toB, toB_emb a, toB_emb b]
  | .atom _ => rfl

/-- Evaluate a kind under level-0 and level-1 valuations. -/
abbrev eval (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (K : (Kind α)) : (Kind α) :=
  K.subst (fun n => emb (θ₀ n)) θ₁

/-- A dyn-free kind evaluates to an Fω kind. -/
def evalB (θ₀ : Nat → (BaseKind α)) : (Kind α) → (BaseKind α)
  | .star => .star
  | .arr a b => .arr (evalB θ₀ a) (evalB θ₀ b)
  | .kvar n => θ₀ n
  | .dvar _ => .star
  | .dyn => .star
  | .atom a => .atom a

omit [DecidableEq α] [AtomOrder α] in
theorem eval_dynFree {θ₀ : Nat → (BaseKind α)} {θ₁ : Nat → (Kind α)} :
    ∀ {K : (Kind α)}, K.DynFree → eval θ₀ θ₁ K = emb (evalB θ₀ K)
  | .star, _ => rfl
  | .arr a b, h => by
      show Kind.arr (eval θ₀ θ₁ a) (eval θ₀ θ₁ b) = _
      rw [eval_dynFree h.1, eval_dynFree h.2]
      rfl
  | .kvar _, _ => rfl
  | .dvar _, h => h.elim
  | .dyn, h => h.elim
  | .atom _, _ => rfl

def θcons₀ (k : (BaseKind α)) (θ : Nat → (BaseKind α)) : Nat → (BaseKind α)
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
def onStar (k : (Kind α)) (c : Cand f) : Sem U k :=
  match k with
  | .star => c
  | k => dflt U k

def packVal (K : (Kind α)) (v : Sem U K) : BVal U :=
  match h : toB K with
  | some k => ⟨k, cast (sem_toB h) v⟩
  | none => ⟨.star, snCand f⟩

def unpackVal (k : (Kind α)) (d : BVal U) : Sem U k :=
  match h : toB k with
  | some k' => cast (sem_toB h).symm (d.get k')
  | none => dflt U k

theorem unpack_pack {K : (Kind α)} {k : (BaseKind α)} (h : toB K = some k) (v : Sem U K) :
    unpackVal K (packVal K v) = v := by
  unfold unpackVal packVal
  split
  · next k' h' =>
      split
      · next k'' h'' =>
          cases h''
          rw [BVal.get_self]
          simp
      · next h'' => cases h''
  · next h' => rw [h] at h'; cases h'

omit [DecidableEq α] in
/-- A fitting kind is closed: it decodes to a fitting base kind. -/
theorem toB_of_fits {a : α} : ∀ {K : (Kind α)}, K.Fits a →
    ∃ k, toB K = some k ∧ k.Fits a
  | .star, _ => ⟨.star, rfl, trivial⟩
  | .arr x y, h => by
      obtain ⟨kx, ex, hx⟩ := toB_of_fits h.1
      obtain ⟨ky, ey, hy⟩ := toB_of_fits h.2
      exact ⟨.arr kx ky, by simp only [toB, ex, ey], hx, hy⟩
  | .atom _, h => ⟨_, rfl, h⟩
  | .kvar _, h => h.elim
  | .dvar _, h => h.elim
  | .dyn, h => h.elim

def apackVal (a : α) (K : (Kind α)) (v : Sem U K) : U.El a :=
  match h : toB K with
  | some k =>
      if hk : k.fits a = true then U.pk a k ((BaseKind.fits_iff a k).1 hk) (cast (sem_toB h) v)
      else U.d a
  | none => U.d a

def aunpackVal (a : α) (k : (Kind α)) (e : U.El a) : Sem U k :=
  match h : toB k with
  | some k' => cast (sem_toB h).symm (U.rd a k' e)
  | none => dflt U k

theorem aunpack_apack {a : α} {K : (Kind α)} (hK : K.Fits a) (v : Sem U K) :
    aunpackVal a K (apackVal a K v) = v := by
  obtain ⟨k, e, hk⟩ := toB_of_fits hK
  unfold aunpackVal apackVal
  split
  · next k' h' =>
      split
      · next k'' h'' =>
          cases h''
          rw [dite_eq_left ((BaseKind.fits_iff a k').2 (by rw [h'] at e; cases e; exact hk))]
          rw [U.rd_pk]
          simp
      · next h'' => cases h''
  · next h' => rw [e] at h'; cases h'

def interp (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U) :
    (Ty α) → (k : (Kind α)) → Sem U k
  | tvar n, k => (ρ n).get k
  | arr A B, k => onStar k (arrCand (interp θ₀ θ₁ ρ A .star) (interp θ₀ θ₁ ρ B .star))
  | all K A, k =>
      onStar k (allT (Sem U (eval θ₀ θ₁ K)) (dflt U _)
        fun X => interp θ₀ θ₁ (scons ⟨eval θ₀ θ₁ K, X⟩ ρ) A .star)
  | lam _ A, k =>
      match k with
      | .arr k₁ k₂ => fun X => interp θ₀ θ₁ (scons ⟨k₁, X⟩ ρ) A k₂
      | k => dflt U k
  | app K A B, k => interp θ₀ θ₁ ρ A (.arr (eval θ₀ θ₁ K) k) (interp θ₀ θ₁ ρ B (eval θ₀ θ₁ K))
  | kall0 A, k => onStar k (allT (BaseKind α) .star fun k₀ => interp (θcons₀ k₀ θ₀) θ₁ ρ A .star)
  | kall1 A, k => onStar k (allT (Kind α) .star fun K => interp θ₀ (Kind.kcons K θ₁) ρ A .star)
  | pack K A, k =>
      match k with
      | .dyn => packVal (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ A (eval θ₀ θ₁ K))
      | k => dflt U k
  | unpack _ X, k => unpackVal k (interp θ₀ θ₁ ρ X .dyn)
  | apack a K A, k =>
      match k with
      | .atom b =>
          if h : a = b then h ▸ apackVal a (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ A (eval θ₀ θ₁ K))
          else U.d b
      | k => dflt U k
  | aunpack a _ X, k => aunpackVal a k (interp θ₀ θ₁ ρ X (.atom a))

theorem interp_apack_atom (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U)
    (a : α) (K : (Kind α)) (A : (Ty α)) (b : α) :
    interp θ₀ θ₁ ρ (Ty.apack a K A) (.atom b) =
      (if h : a = b then h ▸ apackVal a (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ A (eval θ₀ θ₁ K))
       else U.d b) := rfl

def WK (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (Δ : (KCtx α)) (ρ : Nat → SVal U) : Prop :=
  ∀ n, (ρ n).kind = eval θ₀ θ₁ (Δ n)

theorem WK.cons {θ₀ : Nat → (BaseKind α)} {θ₁ : Nat → (Kind α)} {Δ : (KCtx α)} {ρ : Nat → SVal U}
    (h : WK θ₀ θ₁ Δ ρ) (k : (Kind α)) (X : Sem U (eval θ₀ θ₁ k)) :
    WK θ₀ θ₁ (kcons k Δ) (scons ⟨eval θ₀ θ₁ k, X⟩ ρ) := fun n => by
  cases n with
  | zero => rfl
  | succ n => exact h n

omit [DecidableEq α] [AtomOrder α] in
theorem eval_sh₀ (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (k₀ : (BaseKind α)) (K : (Kind α)) :
    eval (θcons₀ k₀ θ₀) θ₁ K.sh₀ = eval θ₀ θ₁ K := by
  unfold eval Kind.sh₀
  rw [Kind.subst_ren]
  rfl

omit [DecidableEq α] [AtomOrder α] in
theorem eval_sh₁ (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (K' K : (Kind α)) :
    eval θ₀ (Kind.kcons K' θ₁) K.sh₁ = eval θ₀ θ₁ K := by
  unfold eval Kind.sh₁
  rw [Kind.subst_ren]
  rfl

theorem WK.klift0 {θ₀ : Nat → (BaseKind α)} {θ₁ : Nat → (Kind α)} {Δ : (KCtx α)} {ρ : Nat → SVal U}
    (h : WK θ₀ θ₁ Δ ρ) (k₀ : (BaseKind α)) : WK (θcons₀ k₀ θ₀) θ₁ Δ.klift0 ρ := fun n => by
  rw [h n]
  exact (eval_sh₀ θ₀ θ₁ k₀ (Δ n)).symm

theorem WK.klift1 {θ₀ : Nat → (BaseKind α)} {θ₁ : Nat → (Kind α)} {Δ : (KCtx α)} {ρ : Nat → SVal U}
    (h : WK θ₀ θ₁ Δ ρ) (K : (Kind α)) : WK θ₀ (Kind.kcons K θ₁) Δ.klift1 ρ := fun n => by
  rw [h n]
  exact (eval_sh₁ θ₀ θ₁ K (Δ n)).symm

/-! ## Renaming and substitution -/

theorem interp_tren : ∀ (A : (Ty α)) (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U)
    (ξ : Nat → Nat) (k : (Kind α)), interp θ₀ θ₁ ρ (tren ξ A) k = interp θ₀ θ₁ (ρ ∘ ξ) A k
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
      | atom _ => rfl
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
      | atom _ => rfl
  | unpack K A, θ₀, θ₁, ρ, ξ, k => by
      show unpackVal k (interp θ₀ θ₁ ρ (tren ξ A) .dyn) = unpackVal k (interp θ₀ θ₁ _ A .dyn)
      rw [interp_tren A]
  | apack a K A, θ₀, θ₁, ρ, ξ, k => by
      cases k with
      | atom b =>
          show interp θ₀ θ₁ ρ (Ty.apack a K (tren ξ A)) (.atom b) = _
          rw [interp_apack_atom, interp_apack_atom, interp_tren A]
      | star => rfl
      | arr _ _ => rfl
      | kvar _ => rfl
      | dvar _ => rfl
      | dyn => rfl
  | aunpack a K A, θ₀, θ₁, ρ, ξ, k => by
      show aunpackVal a k (interp θ₀ θ₁ ρ (tren ξ A) (.atom a)) =
        aunpackVal a k (interp θ₀ θ₁ _ A (.atom a))
      rw [interp_tren A]

omit [DecidableEq α] [AtomOrder α] in
theorem eval_ren (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ξ₀ ξ₁ : Nat → Nat) (K : (Kind α)) :
    eval θ₀ θ₁ (K.ren ξ₀ ξ₁) = eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) K := by
  unfold eval
  rw [Kind.subst_ren]
  rfl

theorem interp_kren : ∀ (A : (Ty α)) (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U)
    (ξ₀ ξ₁ : Nat → Nat) (k : (Kind α)),
    interp θ₀ θ₁ ρ (Ty.kren ξ₀ ξ₁ A) k = interp (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) ρ A k
  | tvar _, _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show onStar k _ = onStar k _
      rw [interp_kren A, interp_kren B]
  | all K A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show onStar k (allT (Sem U (eval θ₀ θ₁ (K.ren ξ₀ ξ₁))) _ _) =
        onStar k (allT (Sem U (eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) K)) _ _)
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
      | atom _ => rfl
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
      | atom _ => rfl
  | unpack K A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show unpackVal k (interp θ₀ θ₁ ρ (Ty.kren ξ₀ ξ₁ A) .dyn) = _
      rw [interp_kren A]
      rfl
  | apack a K A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      cases k with
      | atom b =>
          show interp θ₀ θ₁ ρ (Ty.apack a (K.ren ξ₀ ξ₁) (Ty.kren ξ₀ ξ₁ A)) (.atom b) = _
          rw [interp_apack_atom, interp_apack_atom, interp_kren A, eval_ren]
      | star => rfl
      | arr _ _ => rfl
      | kvar _ => rfl
      | dvar _ => rfl
      | dyn => rfl
  | aunpack a K A, θ₀, θ₁, ρ, ξ₀, ξ₁, k => by
      show aunpackVal a k (interp θ₀ θ₁ ρ (Ty.kren ξ₀ ξ₁ A) (.atom a)) = _
      rw [interp_kren A]
      rfl

theorem eval_subst (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) {σ₀ σ₁ : Nat → (Kind α)}
    (hσ : ∀ n, (σ₀ n).DynFree) (K : (Kind α)) :
    eval θ₀ θ₁ (K.subst σ₀ σ₁) =
      eval (fun n => evalB θ₀ (σ₀ n)) (fun n => eval θ₀ θ₁ (σ₁ n)) K := by
  unfold eval
  rw [Kind.subst_subst]
  congr 1
  funext n
  show eval θ₀ θ₁ (σ₀ n) = emb (evalB θ₀ (σ₀ n))
  exact eval_dynFree (hσ n)

theorem interp_ksubst : ∀ (A : (Ty α)) (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U)
    (σ₀ σ₁ : Nat → (Kind α)) (_ : ∀ n, (σ₀ n).DynFree) (k : (Kind α)),
    interp θ₀ θ₁ ρ (Ty.ksubst σ₀ σ₁ A) k =
      interp (fun n => evalB θ₀ (σ₀ n)) (fun n => eval θ₀ θ₁ (σ₁ n)) ρ A k
  | tvar _, _, _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show onStar k _ = onStar k _
      rw [interp_ksubst A _ _ _ _ _ hσ, interp_ksubst B _ _ _ _ _ hσ]
  | all K A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show onStar k (allT (Sem U (eval θ₀ θ₁ (K.subst σ₀ σ₁))) _ _) = onStar k (allT _ _ _)
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
      | atom _ => rfl
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
            show evalB (θcons₀ k₀ θ₀) ((σ₀ n).ren Nat.succ id) = evalB θ₀ (σ₀ n)
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
        show evalB θ₀ ((σ₀ n).ren id Nat.succ) = evalB θ₀ (σ₀ n)
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
      | atom _ => rfl
  | unpack K A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show unpackVal k (interp θ₀ θ₁ ρ (Ty.ksubst σ₀ σ₁ A) .dyn) = _
      rw [interp_ksubst A _ _ _ _ _ hσ]
      rfl
  | apack a K A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      cases k with
      | atom b =>
          show interp θ₀ θ₁ ρ (Ty.apack a (K.subst σ₀ σ₁) (Ty.ksubst σ₀ σ₁ A)) (.atom b) = _
          rw [interp_apack_atom, interp_apack_atom, interp_ksubst A _ _ _ _ _ hσ,
            eval_subst θ₀ θ₁ hσ]
      | star => rfl
      | arr _ _ => rfl
      | kvar _ => rfl
      | dvar _ => rfl
      | dyn => rfl
  | aunpack a K A, θ₀, θ₁, ρ, σ₀, σ₁, hσ, k => by
      show aunpackVal a k (interp θ₀ θ₁ ρ (Ty.ksubst σ₀ σ₁ A) (.atom a)) = _
      rw [interp_ksubst A _ _ _ _ _ hσ]
      rfl
where
  emb_inj : ∀ {a b : (BaseKind α)}, emb a = emb b → a = b := fun {a b} h => by
    have := congrArg toB h
    rw [toB_emb, toB_emb] at this
    exact Option.some.inj this

theorem interp_subst {Δ : (KCtx α)} {A : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) :
    ∀ (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U) (σ : Nat → (Ty α)),
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

  | @apack Δ a K A _ _ ih =>
      intro θ₀ θ₁ ρ σ
      show interp θ₀ θ₁ ρ (Ty.apack a K (tsubst σ A)) (.atom a) =
        interp θ₀ θ₁ _ (Ty.apack a K A) (.atom a)
      rw [interp_apack_atom, interp_apack_atom, ih θ₀ θ₁ ρ σ]
  | @aunpack Δ a K A _ _ ih =>
      intro θ₀ θ₁ ρ σ
      show aunpackVal a _ (interp θ₀ θ₁ ρ (tsubst σ A) (.atom a)) =
        aunpackVal a _ (interp θ₀ θ₁ _ A (.atom a))
      exact congrArg (aunpackVal a _) (ih θ₀ θ₁ ρ σ)

theorem interp_inst {θ₀ : Nat → (BaseKind α)} {θ₁ : Nat → (Kind α)} {Δ : (KCtx α)} {k k' : (Kind α)} {A : (Ty α)}
    (B : (Ty α)) (hA : Kinded (kcons k Δ) A k') {ρ : Nat → SVal U} (hρ : WK θ₀ θ₁ Δ ρ) :
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

theorem interp_kinst0 (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U) (A : (Ty α))
    {K : (Kind α)} (hK : K.DynFree) (k : (Kind α)) :
    interp θ₀ θ₁ ρ (Ty.kinst0 A K) k = interp (θcons₀ (evalB θ₀ K) θ₀) θ₁ ρ A k := by
  unfold Ty.kinst0
  rw [interp_ksubst A _ _ _ _ _ (fun n => by cases n with
    | zero => exact hK
    | succ n => trivial)]
  congr 1
  funext n
  cases n <;> rfl

theorem interp_kinst1 (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U) (A : (Ty α))
    (K : (Kind α)) (k : (Kind α)) :
    interp θ₀ θ₁ ρ (Ty.kinst1 A K) k = interp θ₀ (Kind.kcons (eval θ₀ θ₁ K) θ₁) ρ A k := by
  unfold Ty.kinst1
  rw [interp_ksubst A θ₀ θ₁ ρ Kind.kvar (Kind.kcons K Kind.dvar) (fun _ => trivial)]
  congr 1
  funext n
  cases n <;> rfl

/-! ## Conversion -/

theorem interp_step {Δ : (KCtx α)} {A B : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) (s : TStep A B)
    {θ₀ : Nat → (BaseKind α)} {θ₁ : Nat → (Kind α)} {ρ : Nat → SVal U} (hρ : WK θ₀ θ₁ Δ ρ) :
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
              have e : toB (eval θ₀ θ₁ K) = some (evalB θ₀ K) := by
                rw [eval_dynFree hK, toB_emb]
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

  | aunpackApack a K A hK =>
      cases h with
      | aunpack hX _ =>
          cases hX with
          | apack hA _ =>
              have eK : eval θ₀ θ₁ K = K := hK.subst_eq _ _
              show aunpackVal a (eval θ₀ θ₁ K) (interp θ₀ θ₁ ρ (Ty.apack a K A) (.atom a)) = _
              rw [interp_apack_atom, dite_eq_left rfl]
              exact aunpack_apack (by rw [eK]; exact hK) _
  | @apack a K A A' _ ih =>
      cases h with
      | apack h₁ _ =>
          show interp θ₀ θ₁ ρ (Ty.apack a K A) (.atom a) = interp θ₀ θ₁ ρ (Ty.apack a K A') (.atom a)
          rw [interp_apack_atom, interp_apack_atom, ih h₁ hρ]
  | @aunpack a K A A' _ ih =>
      cases h with
      | aunpack h₁ _ =>
          show aunpackVal a _ (interp θ₀ θ₁ ρ A (.atom a)) = aunpackVal a _ (interp θ₀ θ₁ ρ A' (.atom a))
          exact congrArg (aunpackVal a _) (ih h₁ hρ)

theorem interp_steps {Δ : (KCtx α)} {A B : (Ty α)} {k : (Kind α)} (h : Kinded Δ A k) (s : TSteps A B)
    {θ₀ : Nat → (BaseKind α)} {θ₁ : Nat → (Kind α)} {ρ : Nat → SVal U} (hρ : WK θ₀ θ₁ Δ ρ) :
    interp θ₀ θ₁ ρ A (eval θ₀ θ₁ k) = interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k) := by
  induction s with
  | refl => rfl
  | step s _ ih => exact (interp_step h s hρ).trans (ih (h.step s))

theorem interp_join {Δ : (KCtx α)} {A B : (Ty α)} {k : (Kind α)} (hA : Kinded Δ A k) (hB : Kinded Δ B k)
    (j : TJoin A B) {θ₀ : Nat → (BaseKind α)} {θ₁ : Nat → (Kind α)} {ρ : Nat → SVal U}
    (hρ : WK θ₀ θ₁ Δ ρ) : interp θ₀ θ₁ ρ A (eval θ₀ θ₁ k) = interp θ₀ θ₁ ρ B (eval θ₀ θ₁ k) := by
  obtain ⟨C, sA, sB⟩ := j
  exact (interp_steps hA sA hρ).trans (interp_steps hB sB hρ).symm

/-! ## Adequacy and strong normalization -/

def OrcOK (U : Universe f α) : Prop :=
  ∀ (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U),
    (interp θ₀ θ₁ ρ (arr Ty.nat Ty.nat) .star).P Tm.orc

theorem adequacy {o : Bool} {Δ : (KCtx α)} {Γ : (Ctx α)} {t : Tm} {A : (Ty α)} (ht : Typed o Δ Γ t A)
    (ho : o = true → OrcOK U) :
    ∀ (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U), WK θ₀ θ₁ Δ ρ →
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
      exact ih θ₀ θ₁ ρ hρ σ h (evalB θ₀ K)
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

theorem sn_of_typed' {o : Bool} {Δ : (KCtx α)} {Γ : (Ctx α)} {t : Tm} {A : (Ty α)}
    (ht : Typed o Δ Γ t A) (ho : o = true → OrcOK U) : SN f t := by
  have h := adequacy ht ho (fun _ => .star) (fun _ => .star)
    (fun n => ⟨eval (fun _ => .star) (fun _ => .star) (Δ n), dflt U _⟩)
    (fun _ => rfl) Tm.var fun n => (interp _ _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact (interp _ _ _ A .star).cr1 h

theorem num_mem (θ₀ : Nat → (BaseKind α)) (θ₁ : Nat → (Kind α)) (ρ : Nat → SVal U) (n : Nat) :
    (interp θ₀ θ₁ ρ Ty.nat .star).P (Tm.num n) := by
  have h := adequacy (f := f)
    (typed_num false (fun _ => Kind.star) (fun _ => Ty.nat) n)
    (fun e => Bool.noConfusion e) θ₀ θ₁ (fun _ => ⟨eval θ₀ θ₁ .star, dflt U _⟩) (fun _ => rfl)
    Tm.var fun k => (interp θ₀ θ₁ _ Ty.nat .star).var k
  rw [Tm.subst_var] at h
  exact h

theorem orcOK (U : Universe f α) : OrcOK U := by
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
theorem sn_of_typed (U : Universe f α) {Δ : (KCtx α)} {Γ : (Ctx α)} {t : Tm} {A : (Ty α)} (ht : Typed true Δ Γ t A) :
    SN f t :=
  sn_of_typed' ht fun _ => orcOK U

end BusyLean.FL
