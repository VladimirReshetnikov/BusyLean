import BusyLean.SystemFLV.Church
import BusyLean.SystemFLV.Candidates
import BusyLean.SystemFLT2.Trees

/-!
# Programs of the ladder with universe levels that read a tree

The reader type of `SystemFLT2`, over the level-extended ladder:

  `readerTy = ∀X. X → (X → X) → ((nat → X) → X) →`
  `           (∀Y. Y → (Y → Y) → ((nat → Y) → Y) → X → Y) → X → X`

A program of this type receives the tree constructors, a recursor over `X`,
and an input of type `X`. After erasure it is applied to `con 0`, `con 1`,
`con 2`, the FT2 recursor and the oracle tree (`FLT2.applyReader`). Adequacy
with `X` set to the tree candidate shows that the result is a well-founded tree
(`wt_of_readerTy`), for every universe over a transitive atom order. The same
holds for programs of the Church tree type, applied to the constructors alone
(`wt_of_treeTy`, as for `SystemFLT`).
-/

namespace BusyLean.FLV

open BusyLean.FL (AtomOrder)
open BusyLean.FLT2 (Universe BaseKind applyReader)
open BusyLean.FT2 (Tm Cand arrCand treeCand natCand WT Orc cz_mem cs_mem cl_mem_of trec_mem
  wt_tsub)
open Ty

variable {f : Orc} {α : Type} [DecidableEq α] [AtomOrder α]

/-- The recursor type over `X = tvar 1`: `∀Y. Y → (Y → Y) → ((nat → Y) → Y) → X → Y`. -/
def recTy : Ty α :=
  all .star (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
    (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (arr (tvar 1) (tvar 0)))))

/-- Programs that build a tree from the constructors, a recursor, and an input tree. -/
def readerTy : Ty α :=
  all .star (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
    (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (arr recTy (arr (tvar 0) (tvar 0))))))

theorem interp_var0 {U : Universe f α} (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α)
    (η : Nat → α) (ρ : Nat → SVal U) (X : Cand f) :
    interp θ₀ θ₁ η (scons ⟨.star, X⟩ ρ) (tvar 0) .star = X :=
  SVal.get_self (U := U) Kind.star X

/-- The interpretation of `nat` has the same members as FT2's numeral candidate. -/
theorem natP_iff {U : Universe f α} (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α) (η : Nat → α)
    (ρ : Nat → SVal U) (a : Tm) :
    (interp θ₀ θ₁ η ρ Ty.nat .star).P a ↔ (natCand f).P a := by
  have key : ∀ X : Cand f, interp θ₀ θ₁ η (scons ⟨.star, X⟩ ρ)
      (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0))) .star =
      arrCand (arrCand X X) (arrCand X X) := by
    intro X
    show arrCand (arrCand (interp θ₀ θ₁ η (scons ⟨.star, X⟩ ρ) (tvar 0) .star) _)
      (arrCand _ _) = _
    rw [interp_var0]
  constructor
  · intro h X
    have hX : (interp θ₀ θ₁ η (scons ⟨.star, X⟩ ρ)
        (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0))) .star).P a := h X
    rwa [key X] at hX
  · intro h X
    show (interp θ₀ θ₁ η (scons ⟨.star, X⟩ ρ)
      (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0))) .star).P a
    rw [key X]
    exact h X

/-! ## Church trees -/

/-- Church-encoded countable trees: `∀X:★. X → (X → X) → ((nat → X) → X) → X`. -/
def treeTy : Ty α :=
  all .star (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
    (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (tvar 0))))

/-- Apply a term to the three tree constructors. -/
def applyCons (t : Tm) : Tm := .app (.app (.app t (.con 0)) (.con 1)) (.con 2)

/-- Membership in the interpretation of `treeTy` gives a well-founded tree. -/
theorem wt_of_interp_treeTy {U : Universe f α} {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α}
    {η : Nat → α} {ρ : Nat → SVal U} {t : Tm} (h : (interp θ₀ θ₁ η ρ treeTy .star).P t) :
    WT f (applyCons t) := by
  have e0 := interp_var0 θ₀ θ₁ η ρ (treeCand f)
  have h2 : (interp θ₀ θ₁ η (scons ⟨.star, treeCand f⟩ ρ) (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
      (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (tvar 0)))) .star).P t := h (treeCand f)
  generalize scons ⟨.star, treeCand f⟩ ρ = ρ' at e0 h2
  have hN : ∀ a, (natCand f).P a → (interp θ₀ θ₁ η ρ' Ty.nat .star).P a :=
    fun a ha => (natP_iff θ₀ θ₁ η ρ' a).2 ha
  have h3 : (arrCand (interp θ₀ θ₁ η ρ' (tvar 0) .star)
      (arrCand (arrCand (interp θ₀ θ₁ η ρ' (tvar 0) .star) (interp θ₀ θ₁ η ρ' (tvar 0) .star))
      (arrCand (arrCand (arrCand (interp θ₀ θ₁ η ρ' Ty.nat .star) (interp θ₀ θ₁ η ρ' (tvar 0) .star))
        (interp θ₀ θ₁ η ρ' (tvar 0) .star)) (interp θ₀ θ₁ η ρ' (tvar 0) .star)))).P t := h2
  rw [e0] at h3
  exact h3 _ cz_mem _ cs_mem _ (cl_mem_of _ hN)

/-- **Programs of the ladder with levels of the Church tree type denote
well-founded trees** (`FLT.wt_of_treeTy`, extended to levels). -/
theorem wt_of_treeTy (U : Universe f α) (htr : LtTrans α) (a₀ : α) {Λ : List (Lvl α)}
    {Δ : KCtx α} {Γ : Ctx α} {t : Tm} (ht : Typed true Λ Δ Γ t treeTy) :
    WT f (applyCons t) := by
  have h := adequacy (U := U) htr ht (fun _ => orcOK htr U) (fun _ => .star) (fun _ => .star)
    (goodVal a₀ Λ)
    (fun n => ⟨eval (fun _ => .star) (fun _ => .star) (goodVal a₀ Λ) (Δ n), dflt U _⟩)
    (goodVal_good a₀ Λ) (fun _ => rfl) Tm.var fun n => (interp _ _ _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact wt_of_interp_treeTy h

/-! ## Readers -/

/-- The FT2 recursor belongs to the recursor type when `X` is the tree candidate. -/
theorem trec_mem_recTy {U : Universe f α} (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α)
    (η : Nat → α) (ρ : Nat → SVal U) :
    (interp θ₀ θ₁ η (scons ⟨.star, treeCand f⟩ ρ) recTy .star).P Tm.trec := by
  intro Y
  show (interp θ₀ θ₁ η (scons ⟨.star, Y⟩ (scons ⟨.star, treeCand f⟩ ρ))
    (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
      (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (arr (tvar 1) (tvar 0))))) .star).P Tm.trec
  have e0 := interp_var0 θ₀ θ₁ η (scons ⟨.star, treeCand f⟩ ρ) Y
  have e1 : interp θ₀ θ₁ η (scons ⟨.star, Y⟩ (scons ⟨.star, treeCand f⟩ ρ)) (tvar 1) .star =
      treeCand f := SVal.get_self (U := U) Kind.star (treeCand f)
  generalize scons ⟨.star, Y⟩ (scons ⟨.star, treeCand f⟩ ρ) = ρ' at e0 e1
  show (arrCand (interp θ₀ θ₁ η ρ' (tvar 0) .star)
    (arrCand (arrCand (interp θ₀ θ₁ η ρ' (tvar 0) .star) (interp θ₀ θ₁ η ρ' (tvar 0) .star))
    (arrCand (arrCand (arrCand (interp θ₀ θ₁ η ρ' Ty.nat .star) (interp θ₀ θ₁ η ρ' (tvar 0) .star))
      (interp θ₀ θ₁ η ρ' (tvar 0) .star))
    (arrCand (interp θ₀ θ₁ η ρ' (tvar 1) .star) (interp θ₀ θ₁ η ρ' (tvar 0) .star))))).P Tm.trec
  rw [e0, e1]
  intro z hz s hs l hl u hu
  exact trec_mem Y hu z s l hz hs fun k hk => hl k fun a ha => hk a ((natP_iff θ₀ θ₁ η ρ' a).1 ha)

/-- Membership in the interpretation of `readerTy` gives a well-founded tree. -/
theorem wt_of_interp_readerTy {U : Universe f α} {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α}
    {η : Nat → α} {ρ : Nat → SVal U} {t : Tm} (h : (interp θ₀ θ₁ η ρ readerTy .star).P t) :
    WT f (applyReader t) := by
  have hR := trec_mem_recTy θ₀ θ₁ η ρ
  have e0 := interp_var0 θ₀ θ₁ η ρ (treeCand f)
  have h2 : (interp θ₀ θ₁ η (scons ⟨.star, treeCand f⟩ ρ) (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
      (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (arr recTy (arr (tvar 0) (tvar 0)))))) .star).P t :=
    h (treeCand f)
  generalize scons ⟨.star, treeCand f⟩ ρ = ρ' at e0 hR h2
  have hN : ∀ a, (natCand f).P a → (interp θ₀ θ₁ η ρ' Ty.nat .star).P a :=
    fun a ha => (natP_iff θ₀ θ₁ η ρ' a).2 ha
  have h3 : (arrCand (interp θ₀ θ₁ η ρ' (tvar 0) .star)
      (arrCand (arrCand (interp θ₀ θ₁ η ρ' (tvar 0) .star) (interp θ₀ θ₁ η ρ' (tvar 0) .star))
      (arrCand (arrCand (arrCand (interp θ₀ θ₁ η ρ' Ty.nat .star) (interp θ₀ θ₁ η ρ' (tvar 0) .star))
        (interp θ₀ θ₁ η ρ' (tvar 0) .star))
      (arrCand (interp θ₀ θ₁ η ρ' recTy .star)
        (arrCand (interp θ₀ θ₁ η ρ' (tvar 0) .star) (interp θ₀ θ₁ η ρ' (tvar 0) .star)))))).P t :=
    h2
  rw [e0] at h3
  exact h3 _ cz_mem _ cs_mem _ (cl_mem_of _ hN) _ hR _ (wt_tsub _ [] rfl)

/-- **Reader programs of the ladder with levels denote well-founded trees.** -/
theorem wt_of_readerTy (U : Universe f α) (htr : LtTrans α) (a₀ : α) {Λ : List (Lvl α)}
    {Δ : KCtx α} {Γ : Ctx α} {t : Tm} (ht : Typed true Λ Δ Γ t readerTy) :
    WT f (applyReader t) := by
  have h := adequacy (U := U) htr ht (fun _ => orcOK htr U) (fun _ => .star) (fun _ => .star)
    (goodVal a₀ Λ)
    (fun n => ⟨eval (fun _ => .star) (fun _ => .star) (goodVal a₀ Λ) (Δ n), dflt U _⟩)
    (goodVal_good a₀ Λ) (fun _ => rfl) Tm.var fun n => (interp _ _ _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact wt_of_interp_readerTy h

end BusyLean.FLV
