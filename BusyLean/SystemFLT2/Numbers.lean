import BusyLean.SystemFLT2.Trees

/-!
# Ladder programs that compute numbers from a tree

A ladder program of the **numeric reader type**

  `natReaderTy = ∀X. (∀Y. Y → (Y → Y) → ((nat → Y) → Y) → X → Y) → X → nat`

receives a recursor over `X` and an input of type `X`, and returns a number.
After erasure it is applied to the FT2 recursor `trec` and the oracle tree
`tsub []`. With `X` set to the tree candidate, adequacy puts the result in the
interpretation of `nat`, so it is strongly normalizing
(`sn_of_natReaderTy`). Its normal form is read off as a numeral.
-/

namespace BusyLean.FLT2

open BusyLean.FL
open BusyLean.FT2 (Tm Cand arrCand treeCand natCand WT Orc SN wt_tsub)
open Ty

variable {f : Orc} {α : Type} [DecidableEq α] [AtomOrder α]

/-- Programs that compute a number from a recursor and an input tree. -/
def natReaderTy : Ty α := all .star (arr recTy (arr (tvar 0) Ty.nat))

/-- Apply a term to the recursor and the oracle tree. -/
def applyNatReader (t : Tm) : Tm := .app (.app t .trec) (.tsub [])

/-- **Numeric reader programs are strongly normalizing.** -/
theorem sn_of_natReaderTy (U : Universe f α) {Δ : KCtx α} {Γ : Ctx α} {t : Tm}
    (ht : Typed true Δ Γ t natReaderTy) : SN f (applyNatReader t) := by
  have h := adequacy (U := U) ht (fun _ => orcOK U) (fun _ => .star) (fun _ => .star)
    (fun n => ⟨eval (fun _ => .star) (fun _ => .star) (Δ n), dflt U _⟩) (fun _ => rfl) Tm.var
    fun n => (interp _ _ _ (Γ n) .star).var n
  rw [Tm.subst_var] at h
  generalize (fun n => (⟨eval (fun _ => .star) (fun _ => .star) (Δ n), dflt U _⟩ : SVal U)) = ρ at h
  have hR := trec_mem_recTy (fun _ => .star) (fun _ => .star) ρ
  have e0 := interp_var0 (fun _ => .star) (fun _ => .star) ρ (treeCand f)
  have h2 : (interp (fun _ => .star) (fun _ => .star) (scons ⟨.star, treeCand f⟩ ρ)
      (arr recTy (arr (tvar 0) Ty.nat)) .star).P t := h (treeCand f)
  generalize scons ⟨.star, treeCand f⟩ ρ = ρ' at e0 hR h2
  have h3 : (arrCand (interp (fun _ => .star) (fun _ => .star) ρ' recTy .star)
      (arrCand (interp (fun _ => .star) (fun _ => .star) ρ' (tvar 0) .star)
        (interp (fun _ => .star) (fun _ => .star) ρ' Ty.nat .star))).P t := h2
  rw [e0] at h3
  exact (interp _ _ ρ' Ty.nat .star).cr1 (h3 _ hR _ (wt_tsub _ [] rfl))

end BusyLean.FLT2
