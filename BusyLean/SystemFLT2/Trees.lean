import BusyLean.SystemFLT2.Church
import BusyLean.SystemFLT2.Transfinite
import BusyLean.SystemFT2.Trees

/-!
# Ladder programs that read a tree

`SystemFLT2` is the ladder language over the terms of System FT2. Its types
are unchanged. A program of the **reader type**

  `readerTy = ∀X. X → (X → X) → ((nat → X) → X) →`
  `           (∀Y. Y → (Y → Y) → ((nat → Y) → Y) → X → Y) → X → X`

receives the three tree constructors, a recursor over `X`, and an input of
type `X`. After erasure it is applied to `con 0`, `con 1`, `con 2`, the FT2
recursor `trec`, and the oracle tree `tsub []`. Adequacy with `X` set to the
tree candidate shows that the result is a well-founded tree
(`wt_of_readerTy`). So ladder programs can recurse over their input tree at
every type their universes provide.
-/

namespace BusyLean.FLT2

open BusyLean.FL
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

/-- Apply a term to the constructors, the recursor, and the oracle tree. -/
def applyReader (t : Tm) : Tm :=
  .app (.app (.app (.app (.app t (.con 0)) (.con 1)) (.con 2)) .trec) (.tsub [])

theorem interp_var0 {U : Universe f α} (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α)
    (ρ : Nat → SVal U) (X : Cand f) :
    interp θ₀ θ₁ (scons ⟨.star, X⟩ ρ) (tvar 0) .star = X :=
  SVal.get_self (U := U) Kind.star X

/-- FL's interpretation of `nat` has the same members as FT2's numeral candidate. -/
theorem natP_iff {U : Universe f α} (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α)
    (ρ : Nat → SVal U) (a : Tm) :
    (interp θ₀ θ₁ ρ Ty.nat .star).P a ↔ (natCand f).P a := by
  have key : ∀ X : Cand f, interp θ₀ θ₁ (scons ⟨.star, X⟩ ρ)
      (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0))) .star =
      arrCand (arrCand X X) (arrCand X X) := by
    intro X
    show arrCand (arrCand (interp θ₀ θ₁ (scons ⟨.star, X⟩ ρ) (tvar 0) .star) _)
      (arrCand _ _) = _
    rw [interp_var0]
  constructor
  · intro h X
    have hX : (interp θ₀ θ₁ (scons ⟨.star, X⟩ ρ)
        (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0))) .star).P a := h X
    rwa [key X] at hX
  · intro h X
    show (interp θ₀ θ₁ (scons ⟨.star, X⟩ ρ)
      (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0))) .star).P a
    rw [key X]
    exact h X

/-- The FT2 recursor belongs to the recursor type when `X` is the tree candidate. -/
theorem trec_mem_recTy {U : Universe f α} (θ₀ : Nat → BaseKind α) (θ₁ : Nat → Kind α)
    (ρ : Nat → SVal U) :
    (interp θ₀ θ₁ (scons ⟨.star, treeCand f⟩ ρ) recTy .star).P Tm.trec := by
  intro Y
  show (interp θ₀ θ₁ (scons ⟨.star, Y⟩ (scons ⟨.star, treeCand f⟩ ρ))
    (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
      (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (arr (tvar 1) (tvar 0))))) .star).P Tm.trec
  have e0 := interp_var0 θ₀ θ₁ (scons ⟨.star, treeCand f⟩ ρ) Y
  have e1 : interp θ₀ θ₁ (scons ⟨.star, Y⟩ (scons ⟨.star, treeCand f⟩ ρ)) (tvar 1) .star =
      treeCand f := SVal.get_self (U := U) Kind.star (treeCand f)
  generalize scons ⟨.star, Y⟩ (scons ⟨.star, treeCand f⟩ ρ) = ρ' at e0 e1
  show (arrCand (interp θ₀ θ₁ ρ' (tvar 0) .star)
    (arrCand (arrCand (interp θ₀ θ₁ ρ' (tvar 0) .star) (interp θ₀ θ₁ ρ' (tvar 0) .star))
    (arrCand (arrCand (arrCand (interp θ₀ θ₁ ρ' Ty.nat .star) (interp θ₀ θ₁ ρ' (tvar 0) .star))
      (interp θ₀ θ₁ ρ' (tvar 0) .star))
    (arrCand (interp θ₀ θ₁ ρ' (tvar 1) .star) (interp θ₀ θ₁ ρ' (tvar 0) .star))))).P Tm.trec
  have hN : ∀ a, (natCand f).P a → (interp θ₀ θ₁ ρ' Ty.nat .star).P a :=
    fun a ha => (natP_iff θ₀ θ₁ ρ' a).2 ha
  rw [e0, e1]
  intro z hz s hs l hl u hu
  exact trec_mem Y hu z s l hz hs fun k hk => hl k fun a ha => hk a ((natP_iff θ₀ θ₁ ρ' a).1 ha)

/-- Membership in the interpretation of `readerTy` gives a well-founded tree. -/
theorem wt_of_interp_readerTy {U : Universe f α} {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α}
    {ρ : Nat → SVal U} {t : Tm} (h : (interp θ₀ θ₁ ρ readerTy .star).P t) :
    WT f (applyReader t) := by
  have hR := trec_mem_recTy θ₀ θ₁ ρ
  have e0 := interp_var0 θ₀ θ₁ ρ (treeCand f)
  have h2 : (interp θ₀ θ₁ (scons ⟨.star, treeCand f⟩ ρ) (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
      (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (arr recTy (arr (tvar 0) (tvar 0)))))) .star).P t :=
    h (treeCand f)
  generalize scons ⟨.star, treeCand f⟩ ρ = ρ' at e0 hR h2
  have hN : ∀ a, (natCand f).P a → (interp θ₀ θ₁ ρ' Ty.nat .star).P a :=
    fun a ha => (natP_iff θ₀ θ₁ ρ' a).2 ha
  have h3 : (arrCand (interp θ₀ θ₁ ρ' (tvar 0) .star)
      (arrCand (arrCand (interp θ₀ θ₁ ρ' (tvar 0) .star) (interp θ₀ θ₁ ρ' (tvar 0) .star))
      (arrCand (arrCand (arrCand (interp θ₀ θ₁ ρ' Ty.nat .star) (interp θ₀ θ₁ ρ' (tvar 0) .star))
        (interp θ₀ θ₁ ρ' (tvar 0) .star))
      (arrCand (interp θ₀ θ₁ ρ' recTy .star)
        (arrCand (interp θ₀ θ₁ ρ' (tvar 0) .star) (interp θ₀ θ₁ ρ' (tvar 0) .star)))))).P t := h2
  rw [e0] at h3
  exact h3 _ cz_mem _ cs_mem _ (cl_mem_of _ hN) _ hR _ (wt_tsub _ [] rfl)

/-- **Reader programs of the ladder denote well-founded trees.** -/
theorem wt_of_readerTy (U : Universe f α) {Δ : KCtx α} {Γ : Ctx α} {t : Tm}
    (ht : Typed true Δ Γ t readerTy) : WT f (applyReader t) := by
  have h := adequacy (U := U) ht (fun _ => orcOK U) (fun _ => .star) (fun _ => .star)
    (fun n => ⟨eval (fun _ => .star) (fun _ => .star) (Δ n), dflt U _⟩) (fun _ => rfl) Tm.var
    fun n => (interp _ _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact wt_of_interp_readerTy h

end BusyLean.FLT2
