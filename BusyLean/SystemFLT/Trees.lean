import BusyLean.SystemFLT.Church
import BusyLean.SystemFLT.Transfinite
import BusyLean.SystemFT.Trees

/-!
# Trees from ladder programs

`SystemFLT` is the ladder language (`SystemFL`) over the terms of `SystemFT`,
so the inert tree constructors `con 0/1/2` are available to the semantics.
The types are unchanged. A program of the Church tree type

  `treeTy = ∀X:★. X → (X → X) → ((nat → X) → X) → X`

is applied, after erasure, to the real constructors. Adequacy with `X` set to
the tree candidate shows the result is a well-founded tree (`wt_of_treeTy`),
so `FT.toTree` reads it off. A ladder over the addresses of a tree `t` thus
produces new trees, which can be longer than `t`.
-/

namespace BusyLean.FLT

open BusyLean.FL
open BusyLean.FT (Tm Cand arrCand treeCand WT cz_mem cs_mem cl_mem_of)
open Ty

variable {f : Nat → Nat} {α : Type} [DecidableEq α] [AtomOrder α]

/-- Church-encoded countable trees: `∀X:★. X → (X → X) → ((nat → X) → X) → X`. -/
def treeTy : Ty α :=
  all .star (arr (tvar 0) (arr (arr (tvar 0) (tvar 0))
    (arr (arr (arr Ty.nat (tvar 0)) (tvar 0)) (tvar 0))))

/-- Apply a term to the three tree constructors. -/
def applyCons (t : Tm) : Tm := .app (.app (.app t (.con 0)) (.con 1)) (.con 2)

/-- Membership in the interpretation of `treeTy` gives a well-founded tree. -/
theorem wt_of_interp_treeTy {U : Universe f α} {θ₀ : Nat → BaseKind α} {θ₁ : Nat → Kind α}
    {ρ : Nat → SVal U} {t : Tm} (h : (interp θ₀ θ₁ ρ treeTy .star).P t) :
    WT f (applyCons t) := by
  have e0 : interp θ₀ θ₁ (scons ⟨.star, treeCand f⟩ ρ) (tvar 0) .star = treeCand f :=
    SVal.get_self (U := U) Kind.star (treeCand f)
  generalize hρ : scons ⟨.star, treeCand f⟩ ρ = ρ' at e0
  have h3 : (arrCand (interp θ₀ θ₁ ρ' (tvar 0) .star)
      (arrCand (arrCand (interp θ₀ θ₁ ρ' (tvar 0) .star) (interp θ₀ θ₁ ρ' (tvar 0) .star))
      (arrCand (arrCand (arrCand (interp θ₀ θ₁ ρ' Ty.nat .star) (interp θ₀ θ₁ ρ' (tvar 0) .star))
        (interp θ₀ θ₁ ρ' (tvar 0) .star)) (interp θ₀ θ₁ ρ' (tvar 0) .star)))).P t := by
    subst hρ; exact h (treeCand f)
  rw [e0] at h3
  exact h3 _ cz_mem _ cs_mem _ (cl_mem_of _ (num_mem _ _ _))

/-- **Ladder programs of the Church tree type denote well-founded trees.** -/
theorem wt_of_treeTy (U : Universe f α) {Δ : KCtx α} {Γ : Ctx α} {t : Tm}
    (ht : Typed true Δ Γ t treeTy) : WT f (applyCons t) := by
  have h := adequacy (U := U) ht (fun _ => orcOK U) (fun _ => .star) (fun _ => .star)
    (fun n => ⟨eval (fun _ => .star) (fun _ => .star) (Δ n), dflt U _⟩) (fun _ => rfl) Tm.var
    fun n => (interp _ _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  exact wt_of_interp_treeTy h

end BusyLean.FLT
