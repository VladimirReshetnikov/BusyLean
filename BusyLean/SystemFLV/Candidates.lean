import BusyLean.SystemFLV.Typing
import BusyLean.SystemFLT2.Candidates

/-!
# Strong normalization of the ladder with universe levels

The model of `SystemFLT2`, extended to levels. It is parametric in the same
`Universe` (atoms, their domains, packing and reading), so the transfinite
universes of `SystemFLT2.Transfinite` serve here unchanged.

A **level valuation** `η` sends level variables to atoms. A kind is evaluated
by substituting its levels by `η` and its kind variables by `θ₀`, `θ₁`. The
domain of the evaluated level family `lfam a k` is the type of functions from
the atoms `c ≤ a` to the domain of `k`:

* bounded quantification `∀b ≤ l. A` is the intersection over the atoms
  `c ≤ η(l)` (the bound is non-strict, so the intersection has an index);
* a level-indexed operator `λb ≤ l. A` is the function `c ↦ ⟦A⟧(η[b := c])`;
* the application of a family to a level `c` checks `c ≤ a` (decidably) and
  applies.

The conversions hold for valuations that respect the bounds of the level
context (`LGood`), whenever the atom order is transitive (`LtTrans`): then
the order the bounds force is sound (`llt_sound`), so a fitting kind evaluates
to a base kind below the atom it is packed into, and a family is applied
inside its bound. Every level context has such a valuation (`goodVal`), so
typed terms are strongly normalizing (`sn_of_typed`).
-/

namespace BusyLean.FLV

open BusyLean.FL (AtomOrder)
open BusyLean.FLT2 (Universe BaseKind SemB BVal allT)
open BusyLean.FT2 (Tm Cand snCand arrCand SN)
open Ty

variable {f : FT2.Orc} {α : Type} [DecidableEq α] [AtomOrder α]

instance (c a : α) : Decidable (LeA c a) :=
  inferInstanceAs (Decidable (c = a ∨ AtomOrder.lt c a = true))

/-- Semantic domains of evaluated kinds. Level and kind variables never occur
in evaluated kinds; they get a junk domain. -/
def Sem (U : Universe f α) : Kind α → Type
  | .star => Cand f
  | .arr a b => Sem U a → Sem U b
  | .dyn => BVal U
  | .atom (.const a) => U.El a
  | .atom (.var _) => Cand f
  | .lfam (.const a) k => (c : α) → LeA c a → Sem U k
  | .lfam (.var _) _ => Cand f
  | .kvar _ => Cand f
  | .dvar _ => Cand f

def dflt (U : Universe f α) : (k : Kind α) → Sem U k
  | .star => snCand f
  | .arr _ b => fun _ => dflt U b
  | .dyn => ⟨.star, snCand f⟩
  | .atom (.const a) => U.d a
  | .atom (.var _) => snCand f
  | .lfam (.const _) k => fun _ _ => dflt U k
  | .lfam (.var _) _ => snCand f
  | .kvar _ => snCand f
  | .dvar _ => snCand f

variable {U : Universe f α}

structure SVal (U : Universe f α) where
  kind : Kind α
  val : Sem U kind

def SVal.get (x : SVal U) (k : Kind α) : Sem U k :=
  if h : x.kind = k then h ▸ x.val else dflt U k

theorem SVal.get_self (k : Kind α) (v : Sem U k) : (SVal.mk k v).get k = v := by
  unfold SVal.get
  rw [dite_eq_left rfl]

theorem SVal.eta {x : SVal U} {k : Kind α} (h : x.kind = k) : SVal.mk k (x.get k) = x := by
  obtain ⟨k', v⟩ := x
  cases h
  rw [SVal.get_self]

def scons (x : SVal U) (ρ : Nat → SVal U) : Nat → SVal U
  | 0 => x
  | n + 1 => ρ n

/-! ## Base kinds -/

def emb : BaseKind α → Kind α
  | .star => .star
  | .arr a b => .arr (emb a) (emb b)
  | .atom a => .atom (.const a)

def toB : Kind α → Option (BaseKind α)
  | .star => some .star
  | .arr a b =>
      match toB a, toB b with
      | some a', some b' => some (.arr a' b')
      | _, _ => none
  | .atom (.const a) => some (.atom a)
  | .atom (.var _) => none
  | .lfam _ _ => none
  | .kvar _ => none
  | .dvar _ => none
  | .dyn => none

theorem sem_toB : ∀ {K : Kind α} {k : BaseKind α}, toB K = some k → Sem U K = SemB f U.El k
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
  | .atom (.const _), k, h => by cases h; rfl
  | .atom (.var _), _, h => nomatch h
  | .lfam _ _, _, h => nomatch h
  | .kvar _, _, h => nomatch h
  | .dvar _, _, h => nomatch h
  | .dyn, _, h => nomatch h

omit [DecidableEq α] [AtomOrder α] in
theorem toB_emb : ∀ k : BaseKind α, toB (emb k) = some k
  | .star => rfl
  | .arr a b => by simp only [emb, toB, toB_emb a, toB_emb b]
  | .atom _ => rfl

omit [DecidableEq α] [AtomOrder α] in
theorem emb_inj {a b : BaseKind α} (h : emb a = emb b) : a = b := by
  have := congrArg toB h
  rw [toB_emb, toB_emb] at this
  exact Option.some.inj this

/-! ## Evaluation of kinds -/

/-- Evaluate a kind: its levels by `η`, then its kind variables by `θ₀`, `θ₁`. -/
abbrev eval (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (K : Kind α) : Kind α :=
  (K.leval η).subst (fun n => emb (θ₀ n)) θ₁

/-- A dyn-free kind evaluates to a base kind. -/
def evalB (θ₀ : Nat → BaseKind α) (η : Nat → α) : Kind α → BaseKind α
  | .star => .star
  | .arr a b => .arr (evalB θ₀ η a) (evalB θ₀ η b)
  | .kvar n => θ₀ n
  | .dvar _ => .star
  | .dyn => .star
  | .atom l => .atom (l.eval η)
  | .lfam _ _ => .star

omit [DecidableEq α] [AtomOrder α] in
theorem eval_dynFree {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α} {η : Nat → α} :
    ∀ {K : Kind α}, K.DynFree → eval θ₀ θ₁ η K = emb (evalB θ₀ η K)
  | .star, _ => rfl
  | .arr a b, h => by
      show Kind.arr (eval θ₀ θ₁ η a) (eval θ₀ θ₁ η b) = _
      rw [eval_dynFree h.1, eval_dynFree h.2]
      rfl
  | .kvar _, _ => rfl
  | .dvar _, h => h.elim
  | .dyn, h => h.elim
  | .atom _, _ => rfl
  | .lfam _ _, h => h.elim

def θcons₀ (k : BaseKind α) (θ : Nat → BaseKind α) : Nat → BaseKind α
  | 0 => k
  | n + 1 => θ n

omit [DecidableEq α] [AtomOrder α] in
theorem eval_sh₀ (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (k₀ : BaseKind α)
    (K : Kind α) : eval (θcons₀ k₀ θ₀) θ₁ η K.sh₀ = eval θ₀ θ₁ η K := by
  unfold eval Kind.sh₀
  rw [Kind.leval_ren, Kind.subst_ren]
  rfl

omit [DecidableEq α] [AtomOrder α] in
theorem eval_sh₁ (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (K' K : Kind α) :
    eval θ₀ (Kind.kcons K' θ₁) η K.sh₁ = eval θ₀ θ₁ η K := by
  unfold eval Kind.sh₁
  rw [Kind.leval_ren, Kind.subst_ren]
  rfl

omit [DecidableEq α] [AtomOrder α] in
theorem eval_lsh (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (c : α) (η : Nat → α) (K : Kind α) :
    eval θ₀ θ₁ (lconsA c η) K.lsh = eval θ₀ θ₁ η K := by
  unfold eval
  rw [Kind.leval_lsh]

omit [DecidableEq α] [AtomOrder α] in
theorem eval_ren (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (ξ₀ ξ₁ : Nat → Nat)
    (K : Kind α) : eval θ₀ θ₁ η (K.ren ξ₀ ξ₁) = eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) η K := by
  unfold eval
  rw [Kind.leval_ren, Kind.subst_ren]
  rfl

omit [DecidableEq α] [AtomOrder α] in
theorem eval_lsubst (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (σ : Nat → Lvl α)
    (K : Kind α) : eval θ₀ θ₁ η (K.lsubst σ) = eval θ₀ θ₁ (fun i => (σ i).eval η) K := by
  unfold eval
  rw [Kind.leval_lsubst]

omit [DecidableEq α] [AtomOrder α] in
theorem eval_subst (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    {σ₀ σ₁ : Nat → Kind α} (hσ : ∀ n, (σ₀ n).DynFree) (K : Kind α) :
    eval θ₀ θ₁ η (K.subst σ₀ σ₁) =
      eval (fun n => evalB θ₀ η (σ₀ n)) (fun n => eval θ₀ θ₁ η (σ₁ n)) η K := by
  unfold eval
  rw [Kind.leval_subst, Kind.subst_subst]
  congr 1
  funext n
  show eval θ₀ θ₁ η (σ₀ n) = emb (evalB θ₀ η (σ₀ n))
  exact eval_dynFree (hσ n)

omit [DecidableEq α] [AtomOrder α] in
theorem evalB_lsh (θ₀ : Nat → BaseKind α) (c : α) (η : Nat → α) :
    ∀ K : Kind α, evalB θ₀ (lconsA c η) K.lsh = evalB θ₀ η K
  | .star => rfl
  | .arr a b => by
      show BaseKind.arr (evalB θ₀ (lconsA c η) a.lsh) (evalB θ₀ (lconsA c η) b.lsh) = _
      rw [evalB_lsh θ₀ c η a, evalB_lsh θ₀ c η b]
      rfl
  | .kvar _ => rfl
  | .dvar _ => rfl
  | .dyn => rfl
  | .atom l => by
      show BaseKind.atom ((l.ren Nat.succ).eval (lconsA c η)) = _
      rw [eval_ren_succ]
      rfl
  | .lfam _ _ => rfl

/-! ## Interpretation -/

/-- A candidate, placed at an expected kind (default unless the kind is `★`). -/
def onStar (k : Kind α) (c : Cand f) : Sem U k :=
  match k with
  | .star => c
  | k => dflt U k

def packVal (K : Kind α) (v : Sem U K) : BVal U :=
  match h : toB K with
  | some k => ⟨k, cast (sem_toB h) v⟩
  | none => ⟨.star, snCand f⟩

def unpackVal (k : Kind α) (d : BVal U) : Sem U k :=
  match h : toB k with
  | some k' => cast (sem_toB h).symm (d.get k')
  | none => dflt U k

theorem unpack_pack {K : Kind α} {k : BaseKind α} (h : toB K = some k) (v : Sem U K) :
    unpackVal K (packVal K v) = v := by
  unfold unpackVal packVal
  split
  · next k' h' =>
      split
      · next k'' h'' =>
          cases h''
          rw [FLT2.BVal.get_self]
          simp
      · next h'' => cases h''
  · next h' => rw [h] at h'; cases h'

omit [DecidableEq α] in
/-- A fitting kind evaluates, under a valuation that respects the bounds, to a
base kind below the evaluated atom. -/
theorem toB_eval_of_fits (htr : LtTrans α) {Λ : List (Lvl α)} {η : Nat → α} (hg : LGood Λ η)
    (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) {l : Lvl α} :
    ∀ {K : Kind α}, K.Fits Λ l → ∃ k, toB (eval θ₀ θ₁ η K) = some k ∧ k.Fits (l.eval η)
  | .star, _ => ⟨.star, rfl, trivial⟩
  | .arr x y, h => by
      obtain ⟨kx, ex, hx⟩ := toB_eval_of_fits htr hg θ₀ θ₁ h.1
      obtain ⟨ky, ey, hy⟩ := toB_eval_of_fits htr hg θ₀ θ₁ h.2
      refine ⟨.arr kx ky, ?_, hx, hy⟩
      show toB (Kind.arr (eval θ₀ θ₁ η x) (eval θ₀ θ₁ η y)) = _
      simp only [toB, ex, ey]
  | .atom b, h => ⟨.atom (b.eval η), rfl, llt_sound htr Λ η b l hg h⟩
  | .kvar _, h => h.elim
  | .dvar _, h => h.elim
  | .dyn, h => h.elim
  | .lfam _ _, h => h.elim

def apackVal (a : α) (K : Kind α) (v : Sem U K) : U.El a :=
  match h : toB K with
  | some k =>
      if hk : k.fits a = true then
        U.pk a k ((FLT2.BaseKind.fits_iff a k).1 hk) (cast (sem_toB h) v)
      else U.d a
  | none => U.d a

def aunpackVal (a : α) (k : Kind α) (e : U.El a) : Sem U k :=
  match h : toB k with
  | some k' => cast (sem_toB h).symm (U.rd a k' e)
  | none => dflt U k

theorem aunpack_apack {a : α} {K : Kind α} {k : BaseKind α} (e : toB K = some k) (hk : k.Fits a)
    (v : Sem U K) : aunpackVal a K (apackVal a K v) = v := by
  unfold aunpackVal apackVal
  split
  · next k' h' =>
      split
      · next k'' h'' =>
          cases h''
          rw [dite_eq_left ((FLT2.BaseKind.fits_iff a k').2 (by rw [h'] at e; cases e; exact hk))]
          rw [U.rd_pk]
          simp
      · next h'' => cases h''
  · next h' => rw [e] at h'; cases h'

/-- Apply a level-indexed operator to an atom: inside its bound it is applied,
outside it gives the default. -/
def lappVal {a : α} {k : Kind α} (F : (c : α) → LeA c a → Sem U k) (c : α) : Sem U k :=
  if h : LeA c a then F c h else dflt U k

theorem lappVal_of_le {a : α} {k : Kind α} (F : (c : α) → LeA c a → Sem U k) {c : α}
    (h : LeA c a) : lappVal F c = F c h := by
  unfold lappVal
  rw [dite_eq_left h]

def interp (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (ρ : Nat → SVal U) :
    Ty α → (k : Kind α) → Sem U k
  | tvar n, k => (ρ n).get k
  | arr A B, k => onStar k (arrCand (interp θ₀ θ₁ η ρ A .star) (interp θ₀ θ₁ η ρ B .star))
  | all K A, k =>
      onStar k (allT (Sem U (eval θ₀ θ₁ η K)) (dflt U _)
        fun X => interp θ₀ θ₁ η (scons ⟨eval θ₀ θ₁ η K, X⟩ ρ) A .star)
  | lam _ A, k =>
      match k with
      | .arr k₁ k₂ => fun X => interp θ₀ θ₁ η (scons ⟨k₁, X⟩ ρ) A k₂
      | k => dflt U k
  | app K A B, k =>
      interp θ₀ θ₁ η ρ A (.arr (eval θ₀ θ₁ η K) k) (interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η K))
  | kall0 A, k =>
      onStar k (allT (BaseKind α) .star fun k₀ => interp (θcons₀ k₀ θ₀) θ₁ η ρ A .star)
  | kall1 A, k =>
      onStar k (allT (Kind α) .star fun K => interp θ₀ (Kind.kcons K θ₁) η ρ A .star)
  | pack K A, k =>
      match k with
      | .dyn => packVal (eval θ₀ θ₁ η K) (interp θ₀ θ₁ η ρ A (eval θ₀ θ₁ η K))
      | k => dflt U k
  | unpack _ X, k => unpackVal k (interp θ₀ θ₁ η ρ X .dyn)
  | apack l K A, k =>
      match k with
      | .atom (.const b) =>
          if h : l.eval η = b then
            h ▸ apackVal (l.eval η) (eval θ₀ θ₁ η K) (interp θ₀ θ₁ η ρ A (eval θ₀ θ₁ η K))
          else U.d b
      | k => dflt U k
  | aunpack l _ X, k =>
      aunpackVal (l.eval η) k (interp θ₀ θ₁ η ρ X (.atom (.const (l.eval η))))
  | lall l A, k =>
      onStar k (allT {c : α // LeA c (l.eval η)} ⟨l.eval η, Or.inl rfl⟩
        fun c => interp θ₀ θ₁ (lconsA c.1 η) ρ A .star)
  | llam _ A, k =>
      match k with
      | .lfam (.const _) k₂ => fun c _ => interp θ₀ θ₁ (lconsA c η) ρ A k₂
      | k => dflt U k
  | lapp l F c, k =>
      lappVal (a := l.eval η) (k := k) (interp θ₀ θ₁ η ρ F (.lfam (.const (l.eval η)) k)) (c.eval η)

theorem interp_apack_atom (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (l : Lvl α) (K : Kind α) (A : Ty α) (b : α) :
    interp θ₀ θ₁ η ρ (Ty.apack l K A) (.atom (.const b)) =
      (if h : l.eval η = b then
        h ▸ apackVal (l.eval η) (eval θ₀ θ₁ η K) (interp θ₀ θ₁ η ρ A (eval θ₀ θ₁ η K))
       else U.d b) := rfl

def WK (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (Δ : KCtx α)
    (ρ : Nat → SVal U) : Prop :=
  ∀ n, (ρ n).kind = eval θ₀ θ₁ η (Δ n)

theorem WK.cons {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α} {η : Nat → α} {Δ : KCtx α}
    {ρ : Nat → SVal U} (h : WK θ₀ θ₁ η Δ ρ) (k : Kind α) (X : Sem U (eval θ₀ θ₁ η k)) :
    WK θ₀ θ₁ η (kcons k Δ) (scons ⟨eval θ₀ θ₁ η k, X⟩ ρ) := fun n => by
  cases n with
  | zero => rfl
  | succ n => exact h n

theorem WK.klift0 {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α} {η : Nat → α} {Δ : KCtx α}
    {ρ : Nat → SVal U} (h : WK θ₀ θ₁ η Δ ρ) (k₀ : BaseKind α) :
    WK (θcons₀ k₀ θ₀) θ₁ η Δ.klift0 ρ := fun n => by
  rw [h n]
  exact (eval_sh₀ θ₀ θ₁ η k₀ (Δ n)).symm

theorem WK.klift1 {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α} {η : Nat → α} {Δ : KCtx α}
    {ρ : Nat → SVal U} (h : WK θ₀ θ₁ η Δ ρ) (K : Kind α) :
    WK θ₀ (Kind.kcons K θ₁) η Δ.klift1 ρ := fun n => by
  rw [h n]
  exact (eval_sh₁ θ₀ θ₁ η K (Δ n)).symm

theorem WK.llift {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α} {η : Nat → α} {Δ : KCtx α}
    {ρ : Nat → SVal U} (h : WK θ₀ θ₁ η Δ ρ) (c : α) : WK θ₀ θ₁ (lconsA c η) Δ.llift ρ := fun n => by
  rw [h n]
  exact (eval_lsh θ₀ θ₁ c η (Δ n)).symm

omit [DecidableEq α] in
theorem LGood.cons {Λ : List (Lvl α)} {η : Nat → α} (hg : LGood Λ η) {l : Lvl α} {c : α}
    (hc : LeA c (l.eval η)) : LGood (l :: Λ) (lconsA c η) := ⟨hc, hg⟩

/-! ## Renaming and substitution -/

omit [DecidableEq α] in
theorem allT_bound_congr {a a' : α} (e : a = a') (F F' : α → Cand f) (hF : ∀ c, F c = F' c) :
    allT {c : α // LeA c a} ⟨a, Or.inl rfl⟩ (fun c => F c.1) =
      allT {c : α // LeA c a'} ⟨a', Or.inl rfl⟩ (fun c => F' c.1) := by
  subst e
  have : F = F' := funext hF
  subst this
  rfl

theorem interp_tren : ∀ (A : Ty α) (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (ξ : Nat → Nat) (k : Kind α),
    interp θ₀ θ₁ η ρ (tren ξ A) k = interp θ₀ θ₁ η (ρ ∘ ξ) A k
  | tvar _, _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, η, ρ, ξ, k => by
      show onStar k _ = onStar k _
      rw [interp_tren A, interp_tren B]
  | all K A, θ₀, θ₁, η, ρ, ξ, k => by
      show onStar k _ = onStar k _
      congr 2; funext X
      rw [interp_tren A]
      congr 1; funext n; cases n <;> rfl
  | lam K A, θ₀, θ₁, η, ρ, ξ, k => by
      cases k with
      | arr k₁ k₂ =>
          funext X
          show interp θ₀ θ₁ η _ (tren _ A) k₂ = interp θ₀ θ₁ η _ A k₂
          rw [interp_tren A]
          congr 1; funext n; cases n <;> rfl
      | _ => rfl
  | app K A B, θ₀, θ₁, η, ρ, ξ, k => by
      show interp θ₀ θ₁ η ρ (tren ξ A) (.arr (eval θ₀ θ₁ η K) k)
          (interp θ₀ θ₁ η ρ (tren ξ B) (eval θ₀ θ₁ η K)) = _
      rw [interp_tren A, interp_tren B]
      rfl
  | kall0 A, θ₀, θ₁, η, ρ, ξ, k => by
      show onStar k _ = onStar k _
      congr 2; funext k₀
      exact interp_tren A _ _ η ρ ξ _
  | kall1 A, θ₀, θ₁, η, ρ, ξ, k => by
      show onStar k _ = onStar k _
      congr 2; funext K
      exact interp_tren A _ _ η ρ ξ _
  | pack K A, θ₀, θ₁, η, ρ, ξ, k => by
      cases k with
      | dyn =>
          show packVal _ (interp θ₀ θ₁ η ρ (tren ξ A) _) = packVal _ (interp θ₀ θ₁ η _ A _)
          rw [interp_tren A]
      | _ => rfl
  | unpack K A, θ₀, θ₁, η, ρ, ξ, k => by
      show unpackVal k (interp θ₀ θ₁ η ρ (tren ξ A) .dyn) = unpackVal k (interp θ₀ θ₁ η _ A .dyn)
      rw [interp_tren A]
  | apack l K A, θ₀, θ₁, η, ρ, ξ, k => by
      cases k with
      | atom l' =>
          cases l' with
          | const b =>
              show interp θ₀ θ₁ η ρ (Ty.apack l K (tren ξ A)) (.atom (.const b)) = _
              rw [interp_apack_atom, interp_apack_atom, interp_tren A]
          | var _ => rfl
      | _ => rfl
  | aunpack l K A, θ₀, θ₁, η, ρ, ξ, k => by
      show aunpackVal (l.eval η) k (interp θ₀ θ₁ η ρ (tren ξ A) (.atom (.const (l.eval η)))) =
        aunpackVal (l.eval η) k (interp θ₀ θ₁ η _ A (.atom (.const (l.eval η))))
      rw [interp_tren A]
  | lall l A, θ₀, θ₁, η, ρ, ξ, k => by
      show onStar k _ = onStar k _
      congr 2; funext c
      exact interp_tren A _ _ _ ρ ξ _
  | llam l A, θ₀, θ₁, η, ρ, ξ, k => by
      cases k with
      | lfam l' k₂ =>
          cases l' with
          | const a =>
              funext c hc
              exact interp_tren A θ₀ θ₁ (lconsA c η) ρ ξ k₂
          | var _ => rfl
      | _ => rfl
  | lapp l A c, θ₀, θ₁, η, ρ, ξ, k => by
      show lappVal (a := l.eval η) (k := k)
          (interp θ₀ θ₁ η ρ (tren ξ A) (.lfam (.const (l.eval η)) k)) (c.eval η) =
        lappVal (a := l.eval η) (k := k)
          (interp θ₀ θ₁ η (ρ ∘ ξ) A (.lfam (.const (l.eval η)) k)) (c.eval η)
      rw [interp_tren A]

theorem interp_kren : ∀ (A : Ty α) (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (ξ₀ ξ₁ : Nat → Nat) (k : Kind α),
    interp θ₀ θ₁ η ρ (Ty.kren ξ₀ ξ₁ A) k = interp (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) η ρ A k
  | tvar _, _, _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show onStar k _ = onStar k _
      rw [interp_kren A, interp_kren B]
  | all K A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show onStar k (allT (Sem U (eval θ₀ θ₁ η (K.ren ξ₀ ξ₁))) _ _) =
        onStar k (allT (Sem U (eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) η K)) _ _)
      rw [eval_ren]
      congr 2; funext X
      rw [interp_kren A]
  | lam K A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      cases k with
      | arr k₁ k₂ => funext X; exact interp_kren A θ₀ θ₁ η _ ξ₀ ξ₁ k₂
      | _ => rfl
  | app K A B, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show interp θ₀ θ₁ η ρ (Ty.kren ξ₀ ξ₁ A) (.arr (eval θ₀ θ₁ η (K.ren ξ₀ ξ₁)) k)
          (interp θ₀ θ₁ η ρ (Ty.kren ξ₀ ξ₁ B) (eval θ₀ θ₁ η (K.ren ξ₀ ξ₁))) = _
      rw [interp_kren A, interp_kren B, eval_ren]
      rfl
  | kall0 A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show onStar k _ = onStar k _
      congr 2; funext k₀
      rw [interp_kren A]
      congr 1; funext n; cases n <;> rfl
  | kall1 A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show onStar k _ = onStar k _
      congr 2; funext K
      rw [interp_kren A]
      congr 1; funext n; cases n <;> rfl
  | pack K A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      cases k with
      | dyn =>
          show packVal (eval θ₀ θ₁ η (K.ren ξ₀ ξ₁))
              (interp θ₀ θ₁ η ρ (Ty.kren ξ₀ ξ₁ A) (eval θ₀ θ₁ η (K.ren ξ₀ ξ₁))) =
            packVal (eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) η K)
              (interp _ _ η ρ A (eval (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) η K))
          rw [interp_kren A, eval_ren]
      | _ => rfl
  | unpack K A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show unpackVal k (interp θ₀ θ₁ η ρ (Ty.kren ξ₀ ξ₁ A) .dyn) = _
      rw [interp_kren A]
      rfl
  | apack l K A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      cases k with
      | atom l' =>
          cases l' with
          | const b =>
              show interp θ₀ θ₁ η ρ (Ty.apack l (K.ren ξ₀ ξ₁) (Ty.kren ξ₀ ξ₁ A)) (.atom (.const b)) = _
              rw [interp_apack_atom, interp_apack_atom, interp_kren A, eval_ren]
          | var _ => rfl
      | _ => rfl
  | aunpack l K A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show aunpackVal (l.eval η) k (interp θ₀ θ₁ η ρ (Ty.kren ξ₀ ξ₁ A) (.atom (.const (l.eval η)))) = _
      rw [interp_kren A]
      rfl
  | lall l A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show onStar k _ = onStar k _
      congr 2; funext c
      exact interp_kren A _ _ _ ρ ξ₀ ξ₁ _
  | llam l A, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      cases k with
      | lfam l' k₂ =>
          cases l' with
          | const a =>
              funext c hc
              exact interp_kren A θ₀ θ₁ (lconsA c η) ρ ξ₀ ξ₁ k₂
          | var _ => rfl
      | _ => rfl
  | lapp l A c, θ₀, θ₁, η, ρ, ξ₀, ξ₁, k => by
      show lappVal (a := l.eval η) (k := k)
          (interp θ₀ θ₁ η ρ (Ty.kren ξ₀ ξ₁ A) (.lfam (.const (l.eval η)) k)) (c.eval η) =
        lappVal (a := l.eval η) (k := k)
          (interp (θ₀ ∘ ξ₀) (θ₁ ∘ ξ₁) η ρ A (.lfam (.const (l.eval η)) k)) (c.eval η)
      rw [interp_kren A]

theorem interp_ksubst : ∀ (A : Ty α) (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (σ₀ σ₁ : Nat → Kind α) (_ : ∀ n, (σ₀ n).DynFree) (k : Kind α),
    interp θ₀ θ₁ η ρ (Ty.ksubst σ₀ σ₁ A) k =
      interp (fun n => evalB θ₀ η (σ₀ n)) (fun n => eval θ₀ θ₁ η (σ₁ n)) η ρ A k
  | tvar _, _, _, _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show onStar k _ = onStar k _
      rw [interp_ksubst A _ _ _ _ _ _ hσ, interp_ksubst B _ _ _ _ _ _ hσ]
  | all K A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show onStar k (allT (Sem U (eval θ₀ θ₁ η (K.subst σ₀ σ₁))) _ _) = onStar k (allT _ _ _)
      rw [eval_subst θ₀ θ₁ η hσ]
      congr 2; funext X
      rw [interp_ksubst A _ _ _ _ _ _ hσ]
  | lam K A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      cases k with
      | arr k₁ k₂ => funext X; exact interp_ksubst A θ₀ θ₁ η _ σ₀ σ₁ hσ k₂
      | _ => rfl
  | app K A B, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show interp θ₀ θ₁ η ρ (Ty.ksubst σ₀ σ₁ A) (.arr (eval θ₀ θ₁ η (K.subst σ₀ σ₁)) k)
          (interp θ₀ θ₁ η ρ (Ty.ksubst σ₀ σ₁ B) (eval θ₀ θ₁ η (K.subst σ₀ σ₁))) = _
      rw [interp_ksubst A _ _ _ _ _ _ hσ, interp_ksubst B _ _ _ _ _ _ hσ, eval_subst θ₀ θ₁ η hσ]
      rfl
  | kall0 A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show onStar k _ = onStar k _
      congr 2; funext k₀
      have hσ' : ∀ n, ((Ty.kup₀ σ₀ σ₁).1 n).DynFree := fun n => by
        cases n with
        | zero => trivial
        | succ n => exact (hσ n).ren _ _
      rw [interp_ksubst A _ _ _ _ _ _ hσ']
      congr 1
      · funext n
        cases n with
        | zero => rfl
        | succ n =>
            show evalB (θcons₀ k₀ θ₀) η ((σ₀ n).ren Nat.succ id) = evalB θ₀ η (σ₀ n)
            have h1 := eval_sh₀ θ₀ θ₁ η k₀ (σ₀ n)
            rw [eval_dynFree (K := (σ₀ n).sh₀) ((hσ n).ren _ _), eval_dynFree (hσ n)] at h1
            exact emb_inj h1
      · funext n
        exact eval_sh₀ θ₀ θ₁ η k₀ (σ₁ n)
  | kall1 A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show onStar k _ = onStar k _
      congr 2; funext K
      have hσ' : ∀ n, ((Ty.kup₁ σ₀ σ₁).1 n).DynFree := fun n => (hσ n).ren _ _
      rw [interp_ksubst A _ _ _ _ _ _ hσ']
      congr 1
      · funext n
        show evalB θ₀ η ((σ₀ n).ren id Nat.succ) = evalB θ₀ η (σ₀ n)
        have h1 := eval_sh₁ θ₀ θ₁ η K (σ₀ n)
        rw [eval_dynFree (K := (σ₀ n).sh₁) ((hσ n).ren _ _), eval_dynFree (hσ n)] at h1
        exact emb_inj h1
      · funext n
        cases n with
        | zero => rfl
        | succ n => exact eval_sh₁ θ₀ θ₁ η K (σ₁ n)
  | pack K A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      cases k with
      | dyn =>
          show packVal (eval θ₀ θ₁ η (K.subst σ₀ σ₁))
              (interp θ₀ θ₁ η ρ (Ty.ksubst σ₀ σ₁ A) (eval θ₀ θ₁ η (K.subst σ₀ σ₁))) = _
          rw [interp_ksubst A _ _ _ _ _ _ hσ, eval_subst θ₀ θ₁ η hσ]
          rfl
      | _ => rfl
  | unpack K A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show unpackVal k (interp θ₀ θ₁ η ρ (Ty.ksubst σ₀ σ₁ A) .dyn) = _
      rw [interp_ksubst A _ _ _ _ _ _ hσ]
      rfl
  | apack l K A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      cases k with
      | atom l' =>
          cases l' with
          | const b =>
              show interp θ₀ θ₁ η ρ (Ty.apack l (K.subst σ₀ σ₁) (Ty.ksubst σ₀ σ₁ A))
                (.atom (.const b)) = _
              rw [interp_apack_atom, interp_apack_atom, interp_ksubst A _ _ _ _ _ _ hσ,
                eval_subst θ₀ θ₁ η hσ]
          | var _ => rfl
      | _ => rfl
  | aunpack l K A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show aunpackVal (l.eval η) k
        (interp θ₀ θ₁ η ρ (Ty.ksubst σ₀ σ₁ A) (.atom (.const (l.eval η)))) = _
      rw [interp_ksubst A _ _ _ _ _ _ hσ]
      rfl
  | lall l A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show onStar k _ = onStar k _
      congr 2; funext c
      rw [interp_ksubst A _ _ _ _ _ _ (fun n => (hσ n).lsubst _)]
      congr 1
      · funext n; exact evalB_lsh θ₀ c.1 η (σ₀ n)
      · funext n; exact eval_lsh θ₀ θ₁ c.1 η (σ₁ n)
  | llam l A, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      cases k with
      | lfam l' k₂ =>
          cases l' with
          | const a =>
              funext c hc
              show interp θ₀ θ₁ (lconsA c η) ρ (Ty.ksubst _ _ A) k₂ = interp _ _ (lconsA c η) ρ A k₂
              rw [interp_ksubst A _ _ _ _ _ _ (fun n => (hσ n).lsubst _)]
              congr 1
              · funext n; exact evalB_lsh θ₀ c η (σ₀ n)
              · funext n; exact eval_lsh θ₀ θ₁ c η (σ₁ n)
          | var _ => rfl
      | _ => rfl
  | lapp l A c, θ₀, θ₁, η, ρ, σ₀, σ₁, hσ, k => by
      show lappVal (a := l.eval η) (k := k)
          (interp θ₀ θ₁ η ρ (Ty.ksubst σ₀ σ₁ A) (.lfam (.const (l.eval η)) k)) (c.eval η) =
        lappVal (a := l.eval η) (k := k)
          (interp (fun n => evalB θ₀ η (σ₀ n)) (fun n => eval θ₀ θ₁ η (σ₁ n)) η ρ A
            (.lfam (.const (l.eval η)) k)) (c.eval η)
      rw [interp_ksubst A _ _ _ _ _ _ hσ]

/-- **Level substitution** is substitution in the valuation. -/
theorem interp_lsubst : ∀ (A : Ty α) (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (σ : Nat → Lvl α) (k : Kind α),
    interp θ₀ θ₁ η ρ (A.lsubst σ) k = interp θ₀ θ₁ (fun i => (σ i).eval η) ρ A k
  | tvar _, _, _, _, _, _, _ => rfl
  | arr A B, θ₀, θ₁, η, ρ, σ, k => by
      show onStar k _ = onStar k _
      rw [interp_lsubst A, interp_lsubst B]
  | all K A, θ₀, θ₁, η, ρ, σ, k => by
      show onStar k (allT (Sem U (eval θ₀ θ₁ η (K.lsubst σ))) _ _) =
        onStar k (allT (Sem U (eval θ₀ θ₁ (fun i => (σ i).eval η) K)) _ _)
      rw [eval_lsubst]
      congr 2; funext X
      rw [interp_lsubst A]
  | lam K A, θ₀, θ₁, η, ρ, σ, k => by
      cases k with
      | arr k₁ k₂ => funext X; exact interp_lsubst A θ₀ θ₁ η _ σ k₂
      | _ => rfl
  | app K A B, θ₀, θ₁, η, ρ, σ, k => by
      show interp θ₀ θ₁ η ρ (A.lsubst σ) (.arr (eval θ₀ θ₁ η (K.lsubst σ)) k)
          (interp θ₀ θ₁ η ρ (B.lsubst σ) (eval θ₀ θ₁ η (K.lsubst σ))) = _
      rw [interp_lsubst A, interp_lsubst B, eval_lsubst]
      rfl
  | kall0 A, θ₀, θ₁, η, ρ, σ, k => by
      show onStar k _ = onStar k _
      congr 2; funext k₀
      exact interp_lsubst A _ _ η ρ σ _
  | kall1 A, θ₀, θ₁, η, ρ, σ, k => by
      show onStar k _ = onStar k _
      congr 2; funext K
      exact interp_lsubst A _ _ η ρ σ _
  | pack K A, θ₀, θ₁, η, ρ, σ, k => by
      cases k with
      | dyn =>
          show packVal (eval θ₀ θ₁ η (K.lsubst σ))
              (interp θ₀ θ₁ η ρ (A.lsubst σ) (eval θ₀ θ₁ η (K.lsubst σ))) =
            packVal (eval θ₀ θ₁ (fun i => (σ i).eval η) K)
              (interp θ₀ θ₁ _ ρ A (eval θ₀ θ₁ (fun i => (σ i).eval η) K))
          rw [interp_lsubst A, eval_lsubst]
      | _ => rfl
  | unpack K A, θ₀, θ₁, η, ρ, σ, k => by
      show unpackVal k (interp θ₀ θ₁ η ρ (A.lsubst σ) .dyn) = unpackVal k (interp θ₀ θ₁ _ ρ A .dyn)
      rw [interp_lsubst A]
  | apack l K A, θ₀, θ₁, η, ρ, σ, k => by
      cases k with
      | atom l' =>
          cases l' with
          | const b =>
              show interp θ₀ θ₁ η ρ (Ty.apack (l.subst σ) (K.lsubst σ) (A.lsubst σ))
                (.atom (.const b)) = _
              rw [interp_apack_atom, interp_apack_atom, interp_lsubst A, eval_lsubst,
                Lvl.eval_subst]
          | var _ => rfl
      | _ => rfl
  | aunpack l K A, θ₀, θ₁, η, ρ, σ, k => by
      show aunpackVal ((l.subst σ).eval η) k
        (interp θ₀ θ₁ η ρ (A.lsubst σ) (.atom (.const ((l.subst σ).eval η)))) = _
      rw [interp_lsubst A, Lvl.eval_subst]
      rfl
  | lall l A, θ₀, θ₁, η, ρ, σ, k => by
      show onStar k _ = onStar k _
      congr 1
      exact allT_bound_congr (Lvl.eval_subst η σ l)
        (fun c => interp θ₀ θ₁ (lconsA c η) ρ (A.lsubst (Lvl.up σ)) .star)
        (fun c => interp θ₀ θ₁ (lconsA c fun i => (σ i).eval η) ρ A .star) fun c => by
          show interp θ₀ θ₁ (lconsA c η) ρ (A.lsubst (Lvl.up σ)) .star = _
          rw [interp_lsubst A]
          congr 1; funext i
          cases i with
          | zero => rfl
          | succ i => exact eval_ren_succ c η (σ i)
  | llam l A, θ₀, θ₁, η, ρ, σ, k => by
      cases k with
      | lfam l' k₂ =>
          cases l' with
          | const a =>
              funext c hc
              show interp θ₀ θ₁ (lconsA c η) ρ (A.lsubst (Lvl.up σ)) k₂ = _
              rw [interp_lsubst A]
              congr 1; funext i
              cases i with
              | zero => rfl
              | succ i => exact eval_ren_succ c η (σ i)
          | var _ => rfl
      | _ => rfl
  | lapp l A c, θ₀, θ₁, η, ρ, σ, k => by
      show lappVal (a := (l.subst σ).eval η)
          (interp θ₀ θ₁ η ρ (A.lsubst σ) (.lfam (.const ((l.subst σ).eval η)) k))
          ((c.subst σ).eval η) = _
      rw [interp_lsubst A, Lvl.eval_subst, Lvl.eval_subst]
      rfl

theorem interp_lsh (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (c : α) (η : Nat → α)
    (ρ : Nat → SVal U) (A : Ty α) (k : Kind α) :
    interp θ₀ θ₁ (lconsA c η) ρ A.lsh k = interp θ₀ θ₁ η ρ A k := by
  rw [interp_lsubst]
  rfl

theorem interp_linst (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (A : Ty α) (c : Lvl α) (k : Kind α) :
    interp θ₀ θ₁ η ρ (A.linst c) k = interp θ₀ θ₁ (lconsA (c.eval η) η) ρ A k := by
  unfold Ty.linst
  rw [interp_lsubst]
  congr 1
  funext i
  cases i <;> rfl

theorem interp_subst {Λ : List (Lvl α)} {Δ : KCtx α} {A : Ty α} {k : Kind α}
    (h : Kinded Λ Δ A k) :
    ∀ (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (ρ : Nat → SVal U)
      (σ : Nat → Ty α),
      interp θ₀ θ₁ η ρ (tsubst σ A) (eval θ₀ θ₁ η k) =
        interp θ₀ θ₁ η
          (fun n => ⟨eval θ₀ θ₁ η (Δ n), interp θ₀ θ₁ η ρ (σ n) (eval θ₀ θ₁ η (Δ n))⟩) A
          (eval θ₀ θ₁ η k) := by
  induction h with
  | tvar n =>
      intro θ₀ θ₁ η ρ σ
      show interp θ₀ θ₁ η ρ (σ n) _ = SVal.get ⟨_, interp θ₀ θ₁ η ρ (σ n) _⟩ _
      rw [SVal.get_self]
  | arr _ _ ih₁ ih₂ =>
      intro θ₀ θ₁ η ρ σ
      show onStar _ (arrCand _ _) = onStar _ (arrCand _ _)
      exact (congrArg (fun a => onStar _ (arrCand a _)) (ih₁ θ₀ θ₁ η ρ σ)).trans
        (congrArg (fun b => onStar _ (arrCand _ b)) (ih₂ θ₀ θ₁ η ρ σ))
  | @all Λ Δ K A _ ih =>
      intro θ₀ θ₁ η ρ σ
      show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
      congr 2; funext X
      have := ih θ₀ θ₁ η (scons ⟨eval θ₀ θ₁ η K, X⟩ ρ) (tup σ)
      refine this.trans ?_
      congr 1; funext n
      cases n with
      | zero =>
          exact congrArg (SVal.mk _) (SVal.get_self _ X)
      | succ n =>
          show SVal.mk (eval θ₀ θ₁ η (Δ n))
              (interp θ₀ θ₁ η (scons ⟨eval θ₀ θ₁ η K, X⟩ ρ) (tren Nat.succ (σ n))
                (eval θ₀ θ₁ η (Δ n))) = _
          rw [interp_tren]
          rfl
  | @lam Λ Δ k₁ k₂ A _ ih =>
      intro θ₀ θ₁ η ρ σ
      funext X
      have := ih θ₀ θ₁ η (scons ⟨eval θ₀ θ₁ η k₁, X⟩ ρ) (tup σ)
      refine this.trans ?_
      congr 1; funext n
      cases n with
      | zero =>
          exact congrArg (SVal.mk _) (SVal.get_self _ X)
      | succ n =>
          show SVal.mk (eval θ₀ θ₁ η (Δ n))
              (interp θ₀ θ₁ η (scons ⟨eval θ₀ θ₁ η k₁, X⟩ ρ) (tren Nat.succ (σ n))
                (eval θ₀ θ₁ η (Δ n))) = _
          rw [interp_tren]
          rfl
  | @app Λ Δ k₁ k₂ A B _ _ ih₁ ih₂ =>
      intro θ₀ θ₁ η ρ σ
      show interp θ₀ θ₁ η ρ (tsubst σ A) (.arr (eval θ₀ θ₁ η k₁) (eval θ₀ θ₁ η k₂))
          (interp θ₀ θ₁ η ρ (tsubst σ B) (eval θ₀ θ₁ η k₁)) = _
      have h₁ := ih₁ θ₀ θ₁ η ρ σ
      have h₂ := ih₂ θ₀ θ₁ η ρ σ
      have e : eval θ₀ θ₁ η (.arr k₁ k₂) = .arr (eval θ₀ θ₁ η k₁) (eval θ₀ θ₁ η k₂) := rfl
      rw [e] at h₁
      rw [h₁, h₂]
      rfl
  | @kall0 Λ Δ A _ ih =>
      intro θ₀ θ₁ η ρ σ
      show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
      congr 2; funext k₀
      have := ih (θcons₀ k₀ θ₀) θ₁ η ρ (fun n => Ty.kren Nat.succ id (σ n))
      refine this.trans ?_
      congr 1; funext n
      show SVal.mk (eval (θcons₀ k₀ θ₀) θ₁ η (Δ n).sh₀)
          (interp (θcons₀ k₀ θ₀) θ₁ η ρ (Ty.kren Nat.succ id (σ n))
            (eval (θcons₀ k₀ θ₀) θ₁ η (Δ n).sh₀)) = _
      rw [eval_sh₀, interp_kren]
      rfl
  | @kall1 Λ Δ A _ ih =>
      intro θ₀ θ₁ η ρ σ
      show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
      congr 2; funext K
      have := ih θ₀ (Kind.kcons K θ₁) η ρ (fun n => Ty.kren id Nat.succ (σ n))
      refine this.trans ?_
      congr 1; funext n
      show SVal.mk (eval θ₀ (Kind.kcons K θ₁) η (Δ n).sh₁)
          (interp θ₀ (Kind.kcons K θ₁) η ρ (Ty.kren id Nat.succ (σ n))
            (eval θ₀ (Kind.kcons K θ₁) η (Δ n).sh₁)) = _
      rw [eval_sh₁, interp_kren]
      rfl
  | @pack Λ Δ K A _ _ ih =>
      intro θ₀ θ₁ η ρ σ
      show packVal (eval θ₀ θ₁ η K) (interp θ₀ θ₁ η ρ (tsubst σ A) (eval θ₀ θ₁ η K)) =
        packVal (eval θ₀ θ₁ η K) (interp θ₀ θ₁ η _ A (eval θ₀ θ₁ η K))
      rw [ih θ₀ θ₁ η ρ σ]
  | @unpack Λ Δ K A _ _ ih =>
      intro θ₀ θ₁ η ρ σ
      show unpackVal _ (interp θ₀ θ₁ η ρ (tsubst σ A) .dyn) = unpackVal _ (interp θ₀ θ₁ η _ A .dyn)
      exact congrArg (unpackVal _) (ih θ₀ θ₁ η ρ σ)
  | @apack Λ Δ l K A _ _ ih =>
      intro θ₀ θ₁ η ρ σ
      show interp θ₀ θ₁ η ρ (Ty.apack l K (tsubst σ A)) (.atom (.const (l.eval η))) =
        interp θ₀ θ₁ η _ (Ty.apack l K A) (.atom (.const (l.eval η)))
      rw [interp_apack_atom, interp_apack_atom, ih θ₀ θ₁ η ρ σ]
  | @aunpack Λ Δ l K A _ _ ih =>
      intro θ₀ θ₁ η ρ σ
      show aunpackVal (l.eval η) _ (interp θ₀ θ₁ η ρ (tsubst σ A) (.atom (.const (l.eval η)))) =
        aunpackVal (l.eval η) _ (interp θ₀ θ₁ η _ A (.atom (.const (l.eval η))))
      exact congrArg (aunpackVal (l.eval η) _) (ih θ₀ θ₁ η ρ σ)
  | @lall Λ Δ l A _ ih =>
      intro θ₀ θ₁ η ρ σ
      show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
      congr 2; funext c
      have := ih θ₀ θ₁ (lconsA c.1 η) ρ (fun n => (σ n).lsh)
      refine this.trans ?_
      congr 1; funext n
      show SVal.mk (eval θ₀ θ₁ (lconsA c.1 η) (Δ n).lsh)
          (interp θ₀ θ₁ (lconsA c.1 η) ρ (σ n).lsh (eval θ₀ θ₁ (lconsA c.1 η) (Δ n).lsh)) = _
      rw [eval_lsh, interp_lsh]
  | @llam Λ Δ l k A _ ih =>
      intro θ₀ θ₁ η ρ σ
      show interp θ₀ θ₁ η ρ (Ty.llam l (tsubst (fun n => (σ n).lsh) A))
          (.lfam (.const (l.eval η)) (eval θ₀ θ₁ η k)) =
        interp θ₀ θ₁ η _ (Ty.llam l A) (.lfam (.const (l.eval η)) (eval θ₀ θ₁ η k))
      funext c hc
      have := ih θ₀ θ₁ (lconsA c η) ρ (fun n => (σ n).lsh)
      rw [eval_lsh θ₀ θ₁ c η k] at this
      refine this.trans ?_
      congr 1; funext n
      show SVal.mk (eval θ₀ θ₁ (lconsA c η) (Δ n).lsh)
          (interp θ₀ θ₁ (lconsA c η) ρ (σ n).lsh (eval θ₀ θ₁ (lconsA c η) (Δ n).lsh)) = _
      rw [eval_lsh, interp_lsh]
  | @lapp Λ Δ l c k A _ _ ih =>
      intro θ₀ θ₁ η ρ σ
      have ih' : interp θ₀ θ₁ η ρ (tsubst σ A) (.lfam (.const (l.eval η)) (eval θ₀ θ₁ η k)) =
          interp θ₀ θ₁ η
            (fun n => ⟨eval θ₀ θ₁ η (Δ n), interp θ₀ θ₁ η ρ (σ n) (eval θ₀ θ₁ η (Δ n))⟩) A
            (.lfam (.const (l.eval η)) (eval θ₀ θ₁ η k)) := ih θ₀ θ₁ η ρ σ
      show lappVal (a := l.eval η) (k := eval θ₀ θ₁ η k)
          (interp θ₀ θ₁ η ρ (tsubst σ A) (.lfam (.const (l.eval η)) (eval θ₀ θ₁ η k))) (c.eval η) =
        lappVal (a := l.eval η) (k := eval θ₀ θ₁ η k)
          (interp θ₀ θ₁ η
            (fun n => ⟨eval θ₀ θ₁ η (Δ n), interp θ₀ θ₁ η ρ (σ n) (eval θ₀ θ₁ η (Δ n))⟩) A
            (.lfam (.const (l.eval η)) (eval θ₀ θ₁ η k))) (c.eval η)
      rw [ih']

theorem interp_inst {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α} {η : Nat → α} {Λ : List (Lvl α)}
    {Δ : KCtx α} {k k' : Kind α} {A : Ty α} (B : Ty α) (hA : Kinded Λ (kcons k Δ) A k')
    {ρ : Nat → SVal U} (hρ : WK θ₀ θ₁ η Δ ρ) :
    interp θ₀ θ₁ η ρ (Ty.inst A B) (eval θ₀ θ₁ η k') =
      interp θ₀ θ₁ η (scons ⟨eval θ₀ θ₁ η k, interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k)⟩ ρ) A
        (eval θ₀ θ₁ η k') := by
  unfold Ty.inst
  rw [interp_subst hA]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => exact SVal.eta (hρ n)

theorem interp_kinst0 (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (A : Ty α) {K : Kind α} (hK : K.DynFree) (k : Kind α) :
    interp θ₀ θ₁ η ρ (Ty.kinst0 A K) k = interp (θcons₀ (evalB θ₀ η K) θ₀) θ₁ η ρ A k := by
  unfold Ty.kinst0
  rw [interp_ksubst A _ _ _ _ _ _ (fun n => by cases n with
    | zero => exact hK
    | succ n => trivial)]
  congr 1
  funext n
  cases n <;> rfl

theorem interp_kinst1 (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (A : Ty α) (K : Kind α) (k : Kind α) :
    interp θ₀ θ₁ η ρ (Ty.kinst1 A K) k = interp θ₀ (Kind.kcons (eval θ₀ θ₁ η K) θ₁) η ρ A k := by
  unfold Ty.kinst1
  rw [interp_ksubst A θ₀ θ₁ η ρ Kind.kvar (Kind.kcons K Kind.dvar) (fun _ => trivial)]
  congr 1
  funext n
  cases n <;> rfl

/-! ## Conversion -/

theorem interp_step (htr : LtTrans α) {Λ : List (Lvl α)} {Δ : KCtx α} {A B : Ty α} {k : Kind α}
    (h : Kinded Λ Δ A k) (s : TStep A B) {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α}
    {η : Nat → α} (hg : LGood Λ η) {ρ : Nat → SVal U} (hρ : WK θ₀ θ₁ η Δ ρ) :
    interp θ₀ θ₁ η ρ A (eval θ₀ θ₁ η k) = interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k) := by
  induction s generalizing Λ Δ k θ₀ θ₁ η ρ with
  | beta k₁ k' A B =>
      cases h with
      | app hA hB =>
          cases hA with
          | lam hA' =>
              show interp θ₀ θ₁ η
                (scons ⟨eval θ₀ θ₁ η k₁, interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k₁)⟩ ρ) A
                (eval θ₀ θ₁ η k) = _
              rw [interp_inst B hA' hρ]
  | unpackPack K A hK =>
      cases h with
      | unpack hX _ =>
          cases hX with
          | pack hA _ =>
              show unpackVal (eval θ₀ θ₁ η K)
                (packVal (eval θ₀ θ₁ η K) (interp θ₀ θ₁ η ρ A (eval θ₀ θ₁ η K))) = _
              have e : toB (eval θ₀ θ₁ η K) = some (evalB θ₀ η K) := by
                rw [eval_dynFree hK, toB_emb]
              exact unpack_pack e _
  | aunpackApack l K A =>
      cases h with
      | aunpack hX hK =>
          cases hX with
          | apack hA _ =>
              obtain ⟨kb, e, hk⟩ := toB_eval_of_fits htr hg θ₀ θ₁ hK
              show aunpackVal (l.eval η) (eval θ₀ θ₁ η K)
                (interp θ₀ θ₁ η ρ (Ty.apack l K A) (.atom (.const (l.eval η)))) = _
              rw [interp_apack_atom, dite_eq_left rfl]
              exact aunpack_apack e hk _
  | lbeta l l' A c =>
      cases h with
      | lapp hF hc =>
          cases hF with
          | llam hA =>
              have hle := lle_sound htr hg hc
              show lappVal (a := l.eval η) (k := eval θ₀ θ₁ η k)
                (fun c' _ => interp θ₀ θ₁ (lconsA c' η) ρ A (eval θ₀ θ₁ η k)) (c.eval η) = _
              rw [lappVal_of_le _ hle, interp_linst]
  | arrL _ _ ih =>
      cases h with
      | arr h₁ _ =>
          have e := ih h₁ hg hρ
          show onStar _ (arrCand _ _) = onStar _ (arrCand _ _)
          exact congrArg (fun c => onStar _ (arrCand c _)) e
  | arrR _ _ ih =>
      cases h with
      | arr _ h₂ =>
          have e := ih h₂ hg hρ
          show onStar _ (arrCand _ _) = onStar _ (arrCand _ _)
          exact congrArg (fun c => onStar _ (arrCand _ c)) e
  | all K _ ih =>
      cases h with
      | all h₁ =>
          show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
          congr 2; funext X
          exact ih h₁ hg (hρ.cons K X)
  | lam K _ ih =>
      cases h with
      | lam h₁ => funext X; exact ih h₁ hg (hρ.cons K X)
  | @appL k' A A' B _ ih =>
      cases h with
      | app h₁ _ =>
          show interp θ₀ θ₁ η ρ A (.arr (eval θ₀ θ₁ η k') (eval θ₀ θ₁ η k))
              (interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k')) =
            interp θ₀ θ₁ η ρ A' (.arr (eval θ₀ θ₁ η k') (eval θ₀ θ₁ η k))
              (interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k'))
          have := ih h₁ hg hρ
          have e : eval θ₀ θ₁ η (.arr k' k) = .arr (eval θ₀ θ₁ η k') (eval θ₀ θ₁ η k) := rfl
          rw [e] at this
          rw [this]
  | @appR k' A B B' _ ih =>
      cases h with
      | app _ h₂ =>
          show interp θ₀ θ₁ η ρ A (.arr (eval θ₀ θ₁ η k') (eval θ₀ θ₁ η k))
              (interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k')) =
            interp θ₀ θ₁ η ρ A (.arr (eval θ₀ θ₁ η k') (eval θ₀ θ₁ η k))
              (interp θ₀ θ₁ η ρ B' (eval θ₀ θ₁ η k'))
          rw [ih h₂ hg hρ]
  | kall0 _ ih =>
      cases h with
      | kall0 h₁ =>
          show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
          congr 2; funext k₀
          exact ih h₁ hg (hρ.klift0 k₀)
  | kall1 _ ih =>
      cases h with
      | kall1 h₁ =>
          show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
          congr 2; funext K
          exact ih h₁ hg (hρ.klift1 K)
  | @pack K A A' _ ih =>
      cases h with
      | pack h₁ _ =>
          show packVal (eval θ₀ θ₁ η K) (interp θ₀ θ₁ η ρ A (eval θ₀ θ₁ η K)) =
            packVal (eval θ₀ θ₁ η K) (interp θ₀ θ₁ η ρ A' (eval θ₀ θ₁ η K))
          rw [ih h₁ hg hρ]
  | @unpack K A A' _ ih =>
      cases h with
      | unpack h₁ _ =>
          show unpackVal _ (interp θ₀ θ₁ η ρ A .dyn) = unpackVal _ (interp θ₀ θ₁ η ρ A' .dyn)
          exact congrArg (unpackVal _) (ih h₁ hg hρ)
  | @apack l K A A' _ ih =>
      cases h with
      | apack h₁ _ =>
          show interp θ₀ θ₁ η ρ (Ty.apack l K A) (.atom (.const (l.eval η))) =
            interp θ₀ θ₁ η ρ (Ty.apack l K A') (.atom (.const (l.eval η)))
          rw [interp_apack_atom, interp_apack_atom, ih h₁ hg hρ]
  | @aunpack l K A A' _ ih =>
      cases h with
      | aunpack h₁ _ =>
          show aunpackVal (l.eval η) _ (interp θ₀ θ₁ η ρ A (.atom (.const (l.eval η)))) =
            aunpackVal (l.eval η) _ (interp θ₀ θ₁ η ρ A' (.atom (.const (l.eval η))))
          exact congrArg (aunpackVal (l.eval η) _) (ih h₁ hg hρ)
  | lall l _ ih =>
      cases h with
      | lall h₁ =>
          show onStar _ (allT _ _ _) = onStar _ (allT _ _ _)
          congr 2; funext c
          exact ih h₁ (hg.cons c.2) (hρ.llift c.1)
  | @llam l A A' _ ih =>
      cases h with
      | @llam _ _ _ k₂ _ h₁ =>
          show interp θ₀ θ₁ η ρ (Ty.llam l A) (.lfam (.const (l.eval η)) (eval θ₀ θ₁ η k₂)) =
            interp θ₀ θ₁ η ρ (Ty.llam l A') (.lfam (.const (l.eval η)) (eval θ₀ θ₁ η k₂))
          funext c hc
          have := ih h₁ (hg.cons hc) (hρ.llift c)
          rw [eval_lsh θ₀ θ₁ c η k₂] at this
          exact this
  | @lapp l A A' c _ ih =>
      cases h with
      | lapp h₁ _ =>
          exact congrArg (fun F => lappVal F (c.eval η)) (ih h₁ hg hρ)

theorem interp_steps (htr : LtTrans α) {Λ : List (Lvl α)} {Δ : KCtx α} {A B : Ty α} {k : Kind α}
    (h : Kinded Λ Δ A k) (s : TSteps A B) {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α}
    {η : Nat → α} (hg : LGood Λ η) {ρ : Nat → SVal U} (hρ : WK θ₀ θ₁ η Δ ρ) :
    interp θ₀ θ₁ η ρ A (eval θ₀ θ₁ η k) = interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k) := by
  induction s with
  | refl => rfl
  | step s _ ih => exact (interp_step htr h s hg hρ).trans (ih (h.step htr s))

theorem interp_join (htr : LtTrans α) {Λ : List (Lvl α)} {Δ : KCtx α} {A B : Ty α} {k : Kind α}
    (hA : Kinded Λ Δ A k) (hB : Kinded Λ Δ B k) (j : TJoin A B) {θ₀ : Nat → BaseKind α}
    {θ₁ : Nat → Kind α} {η : Nat → α} (hg : LGood Λ η) {ρ : Nat → SVal U}
    (hρ : WK θ₀ θ₁ η Δ ρ) :
    interp θ₀ θ₁ η ρ A (eval θ₀ θ₁ η k) = interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k) := by
  obtain ⟨C, sA, sB⟩ := j
  exact (interp_steps htr hA sA hg hρ).trans (interp_steps htr hB sB hg hρ).symm

/-! ## Adequacy and strong normalization -/

def OrcOK (U : Universe f α) : Prop :=
  ∀ (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (ρ : Nat → SVal U),
    (interp θ₀ θ₁ η ρ (arr Ty.nat Ty.nat) .star).P Tm.orc

theorem adequacy (htr : LtTrans α) {o : Bool} {Λ : List (Lvl α)} {Δ : KCtx α} {Γ : Ctx α} {t : Tm}
    {A : Ty α} (ht : Typed o Λ Δ Γ t A) (ho : o = true → OrcOK U) :
    ∀ (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α) (ρ : Nat → SVal U),
      LGood Λ η → WK θ₀ θ₁ η Δ ρ →
      ∀ (σ : Nat → Tm), (∀ n, (interp θ₀ θ₁ η ρ (Γ n) .star).P (σ n)) →
        (interp θ₀ θ₁ η ρ A .star).P (Tm.subst σ t) := by
  induction ht with
  | var n => intro θ₀ θ₁ η ρ _ _ σ h; exact h n
  | lam _ ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h
      refine FT2.lam_mem fun a ha => ?_
      rw [Tm.subst_beta]
      exact ih θ₀ θ₁ η ρ hg hρ (Tm.cons a σ) fun n => by
        cases n with
        | zero => exact ha
        | succ n => exact h n
  | app _ _ ih₁ ih₂ =>
      intro θ₀ θ₁ η ρ hg hρ σ h
      exact ih₁ θ₀ θ₁ η ρ hg hρ σ h _ (ih₂ θ₀ θ₁ η ρ hg hρ σ h)
  | @gen Λ Δ Γ k A t _ ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h X
      refine ih θ₀ θ₁ η (scons ⟨eval θ₀ θ₁ η k, X⟩ ρ) hg (hρ.cons k X) σ fun n => ?_
      show (interp θ₀ θ₁ η (scons ⟨eval θ₀ θ₁ η k, X⟩ ρ) (tren Nat.succ (Γ n)) .star).P (σ n)
      rw [interp_tren]
      exact h n
  | @inst Λ Δ Γ k A t B _ hA _ ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h
      have hall := ih θ₀ θ₁ η ρ hg hρ σ h (interp θ₀ θ₁ η ρ B (eval θ₀ θ₁ η k))
      have e := interp_inst (f := f) B hA hρ (k' := .star)
      show (interp θ₀ θ₁ η ρ (Ty.inst A B) (eval θ₀ θ₁ η .star)).P _
      rw [e]
      exact hall
  | conv _ hA hB j ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h
      have e := interp_join (f := f) htr hA hB j hg hρ
      show (interp θ₀ θ₁ η ρ _ (eval θ₀ θ₁ η .star)).P _
      rw [← e]
      exact ih θ₀ θ₁ η ρ hg hρ σ h
  | @kgen0 Λ Δ Γ A t _ ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h k₀
      refine ih (θcons₀ k₀ θ₀) θ₁ η ρ hg (hρ.klift0 k₀) σ fun n => ?_
      show (interp (θcons₀ k₀ θ₀) θ₁ η ρ (Ty.kren Nat.succ id (Γ n)) .star).P (σ n)
      rw [interp_kren]
      exact h n
  | @kinst0 Λ Δ Γ A t K _ hK ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h
      rw [interp_kinst0 θ₀ θ₁ η ρ A hK]
      exact ih θ₀ θ₁ η ρ hg hρ σ h (evalB θ₀ η K)
  | @kgen1 Λ Δ Γ A t _ ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h K
      refine ih θ₀ (Kind.kcons K θ₁) η ρ hg (hρ.klift1 K) σ fun n => ?_
      show (interp θ₀ (Kind.kcons K θ₁) η ρ (Ty.kren id Nat.succ (Γ n)) .star).P (σ n)
      rw [interp_kren]
      exact h n
  | @kinst1 Λ Δ Γ A t K _ ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h
      rw [interp_kinst1]
      exact ih θ₀ θ₁ η ρ hg hρ σ h (eval θ₀ θ₁ η K)
  | @lgen Λ Δ Γ l A t _ ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h c
      refine ih θ₀ θ₁ (lconsA c.1 η) ρ (hg.cons c.2) (hρ.llift c.1) σ fun n => ?_
      show (interp θ₀ θ₁ (lconsA c.1 η) ρ (Γ n).lsh .star).P (σ n)
      rw [interp_lsh]
      exact h n
  | @linst Λ Δ Γ l A t c _ hc ih =>
      intro θ₀ θ₁ η ρ hg hρ σ h
      rw [interp_linst]
      exact ih θ₀ θ₁ η ρ hg hρ σ h ⟨c.eval η, lle_sound htr hg hc⟩
  | orc e => intro θ₀ θ₁ η ρ _ _ σ _; exact ho e θ₀ θ₁ η ρ

/-- A valuation that respects the bounds: every level variable at its bound. -/
def goodVal (a₀ : α) : List (Lvl α) → Nat → α
  | [] => fun _ => a₀
  | l :: Λ => lconsA (l.eval (goodVal a₀ Λ)) (goodVal a₀ Λ)

omit [DecidableEq α] in
theorem goodVal_good (a₀ : α) : ∀ Λ : List (Lvl α), LGood Λ (goodVal a₀ Λ)
  | [] => trivial
  | _ :: Λ => (goodVal_good a₀ Λ).cons (Or.inl rfl)

theorem sn_of_typed' (htr : LtTrans α) (a₀ : α) {o : Bool} {Λ : List (Lvl α)} {Δ : KCtx α}
    {Γ : Ctx α} {t : Tm} {A : Ty α} (ht : Typed o Λ Δ Γ t A) (ho : o = true → OrcOK U) :
    SN f t := by
  have h := adequacy htr ht ho (fun _ => .star) (fun _ => .star) (goodVal a₀ Λ)
    (fun n => ⟨eval (fun _ => .star) (fun _ => .star) (goodVal a₀ Λ) (Δ n), dflt U _⟩)
    (goodVal_good a₀ Λ) (fun _ => rfl) Tm.var fun n => (interp _ _ _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact (interp _ _ _ _ A .star).cr1 h

theorem num_mem (htr : LtTrans α) (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (n : Nat) : (interp θ₀ θ₁ η ρ Ty.nat .star).P (Tm.num n) := by
  have h := adequacy (f := f) htr
    (typed_num false [] (fun _ => Kind.star) (fun _ => Ty.nat) n)
    (fun e => Bool.noConfusion e) θ₀ θ₁ η (fun _ => ⟨eval θ₀ θ₁ η .star, dflt U _⟩) trivial
    (fun _ => rfl) Tm.var fun k => (interp θ₀ θ₁ η _ Ty.nat .star).var k
  rw [Tm.subst_var] at h
  exact h

theorem orcOK (htr : LtTrans α) (U : Universe f α) : OrcOK U := by
  intro θ₀ θ₁ η ρ a ha
  have hsn := (interp θ₀ θ₁ η ρ Ty.nat .star).cr1 ha
  revert ha
  induction hsn with
  | intro a _ ih =>
      intro ha
      refine (interp θ₀ θ₁ η ρ Ty.nat .star).cr3
        (by simp [FT2.Neutral, FT2.neutralB, FT2.ctorHead, FT2.trecDepth]) fun v s => ?_
      cases s with
      | delta n => exact num_mem htr θ₀ θ₁ η ρ (f.nat n)
      | appL _ s => exact nomatch s
      | appR _ s => exact ih _ s ((interp θ₀ θ₁ η ρ Ty.nat .star).cr2 ha s)

/-- **Strong normalization of the ladder with universe levels**, for every
universe over a transitive atom order. -/
theorem sn_of_typed (U : Universe f α) (htr : LtTrans α) (a₀ : α) {Λ : List (Lvl α)} {Δ : KCtx α}
    {Γ : Ctx α} {t : Tm} {A : Ty α} (ht : Typed true Λ Δ Γ t A) : SN f t :=
  sn_of_typed' (U := U) htr a₀ ht fun _ => orcOK htr U

end BusyLean.FLV
