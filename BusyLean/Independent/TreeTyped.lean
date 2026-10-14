import BusyLean.Independent.TreeEmbedding
import BusyLean.Independent.TTyped

/-!
# `TT` as Church-style ladder programs

The tree type is `∀X. X → (X → X) → ((nat → X) → X) → X`. `trTC` translates
a `TT` term into the System F fragment of the ladder language. It erases to
`utrT` (`erase_trTC`), and the ladder's type checker accepts it at every fuel
(`infer_trTC`).
-/

namespace BusyLean.Indep.TT

open BusyLean.FL
open BusyLean.Fw (nth?)
open BusyLean.Indep.Emb (Good good_nat infer_lam infer_app infer_tlam infer_tapp zeroC succC recC
  infer_zeroC infer_succC infer_recC)

variable {α : Type} [DecidableEq α] [AtomOrder α]

/-! ## Types -/

abbrev tX : FL.Ty α := .tvar 0
abbrev tXX : FL.Ty α := .arr tX tX
abbrev tL : FL.Ty α := .arr (.arr FL.Ty.nat tX) tX
abbrev treeBody : FL.Ty α := .arr tX (.arr tXX (.arr tL tX))

/-- `∀X. X → (X → X) → ((nat → X) → X) → X`. -/
def treeTyC : FL.Ty α := .all .star treeBody

theorem good_treeTyC : Good (treeTyC : FL.Ty α) where
  ren _ := rfl
  subst _ := rfl
  nf := rfl
  kind _ := rfl

def tyTT : Ty → FL.Ty α
  | .nat => FL.Ty.nat
  | .tree => treeTyC
  | .arr a b => .arr (tyTT a) (tyTT b)

theorem good_tyTT : ∀ σ : Ty, Good (tyTT σ : FL.Ty α)
  | .nat => good_nat
  | .tree => good_treeTyC
  | .arr a b => (good_tyTT a).arr (good_tyTT b)

/-! ## Combinators -/

def app3C (u z s l : CTm α) : CTm α := .app (.app (.app u z) s) l

def tzeroC : CTm α := .tlam .star (.lam tX (.lam tXX (.lam tL (.var 2))))

def tsuccC : CTm α :=
  .lam treeTyC (.tlam .star (.lam tX (.lam tXX (.lam tL
    (.app (.var 1) (app3C (.tapp (.var 3) tX) (.var 2) (.var 1) (.var 0)))))))

def tlimC : CTm α :=
  .lam (.arr FL.Ty.nat treeTyC) (.tlam .star (.lam tX (.lam tXX (.lam tL
    (.app (.var 0) (.lam FL.Ty.nat
      (app3C (.tapp (.app (.var 4) (.var 0)) tX) (.var 3) (.var 2) (.var 1))))))))

def foldC (R : FL.Ty α) : CTm α :=
  .lam R (.lam (.arr R R) (.lam (.arr (.arr FL.Ty.nat R) R) (.lam treeTyC
    (app3C (.tapp (.var 0) R) (.var 3) (.var 2) (.var 1)))))

def trTC : {Γ : List Ty} → {σ : Ty} → Tm Γ σ → CTm α
  | _, _, .var v => .var v.idx
  | _, _, @Tm.lam _ a _ b => .lam (tyTT a) (trTC b)
  | _, _, .app s u => .app (trTC s) (trTC u)
  | _, _, .zero => zeroC
  | _, _, .succ => succC
  | _, _, .nrec r => recC (tyTT r)
  | _, _, .tzero => tzeroC
  | _, _, .tsucc => tsuccC
  | _, _, .tlim => tlimC
  | _, _, .fold r => foldC (tyTT r)

omit [DecidableEq α] [AtomOrder α] in
theorem erase_trTC : ∀ {Γ : List Ty} {σ : Ty} (t : Tm Γ σ), erase (trTC t : CTm α) = utrT t
  | _, _, .var _ => rfl
  | _, _, .lam b => congrArg F.Tm.lam (erase_trTC b)
  | _, _, .app s u => by
      show F.Tm.app (erase (trTC s : CTm α)) (erase (trTC u : CTm α)) = _
      rw [erase_trTC s, erase_trTC u]; rfl
  | _, _, .zero => rfl
  | _, _, .succ => rfl
  | _, _, .nrec _ => rfl
  | _, _, .tzero => rfl
  | _, _, .tsucc => rfl
  | _, _, .tlim => rfl
  | _, _, .fold _ => rfl

/-! ## Typing -/

section Typing

variable {fuel : Nat}

theorem kind_tL (Δ : List (Kind α)) : inferKind (.star :: Δ) (tL : FL.Ty α) = some .star := rfl

theorem infer_tzeroC (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ tzeroC = some treeTyC :=
  infer_tlam (infer_lam rfl (infer_lam rfl (infer_lam (kind_tL Δ) rfl)))

/-- Applying a variable of tree type to the type variable and three arguments. -/
theorem infer_app3_tree {Δ : List (Kind α)} {Γ : List (FL.Ty α)} {t : CTm α}
    (ht : infer fuel (.star :: Δ) Γ t = some treeTyC)
    (hz : infer fuel (.star :: Δ) Γ (.var 2) = some tX)
    (hs : infer fuel (.star :: Δ) Γ (.var 1) = some tXX)
    (hl : infer fuel (.star :: Δ) Γ (.var 0) = some tL) :
    infer fuel (.star :: Δ) Γ (app3C (.tapp t tX) (.var 2) (.var 1) (.var 0)) = some tX := by
  have h1 : infer fuel (.star :: Δ) Γ (.tapp t tX) = some treeBody :=
    infer_tapp (A := treeBody) ht rfl rfl
  exact infer_app (infer_app (infer_app h1 hz rfl) hs rfl) hl rfl

theorem infer_tsuccC (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ tsuccC = some (.arr treeTyC treeTyC) := by
  refine infer_lam (good_treeTyC.kind Δ) (infer_tlam (infer_lam rfl (infer_lam rfl
    (infer_lam (kind_tL Δ) ?_))))
  refine infer_app (A := tX) rfl ?_ rfl
  exact infer_app3_tree rfl rfl rfl rfl

theorem infer_tlimC (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ tlimC = some (.arr (.arr FL.Ty.nat treeTyC) treeTyC) := by
  refine infer_lam ((good_nat.arr good_treeTyC).kind Δ) (infer_tlam (infer_lam rfl (infer_lam rfl
    (infer_lam (kind_tL Δ) ?_))))
  refine infer_app (A := .arr FL.Ty.nat tX) rfl ?_ rfl
  refine infer_lam rfl ?_
  have hg : infer fuel (.star :: Δ)
      (FL.Ty.nat :: tL :: tXX :: tX :: (FL.Ty.arr FL.Ty.nat treeTyC :: Γ).map (Ty.tren Nat.succ))
      (.app (.var 4) (.var 0)) = some treeTyC :=
    infer_app (A := FL.Ty.nat) rfl rfl rfl
  have h1 := infer_tapp (A := treeBody) (X := tX) hg rfl rfl
  exact infer_app (infer_app (infer_app h1 rfl rfl) rfl rfl) rfl rfl

theorem infer_foldC {R : FL.Ty α} (hR : Good R) (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ (foldC R) =
      some (.arr R (.arr (.arr R R) (.arr (.arr (.arr FL.Ty.nat R) R) (.arr treeTyC R)))) := by
  have hRR : Good (FL.Ty.arr R R) := hR.arr hR
  have hL : Good (FL.Ty.arr (.arr FL.Ty.nat R) R) := (good_nat.arr hR).arr hR
  refine infer_lam (hR.kind Δ) (infer_lam (hRR.kind Δ) (infer_lam (hL.kind Δ)
    (infer_lam (good_treeTyC.kind Δ) ?_)))
  have h1 : infer fuel Δ (treeTyC :: .arr (.arr FL.Ty.nat R) R :: .arr R R :: R :: Γ)
      (.tapp (.var 0) R) = some (.arr R (.arr (.arr R R) (.arr (.arr (.arr FL.Ty.nat R) R) R))) := by
    have h := infer_tapp (A := treeBody) (X := R) (fuel := fuel) (Δ := Δ)
      (Γ := treeTyC :: .arr (.arr FL.Ty.nat R) R :: .arr R R :: R :: Γ) (t := .var 0) rfl rfl (hR.kind Δ)
    rw [h]
    rfl
  exact infer_app (infer_app (infer_app h1 rfl (hR.arr ((hRR).arr (hL.arr hR))).nf) rfl
    (hRR.arr (hL.arr hR)).nf) rfl (hL.arr hR).nf

omit [DecidableEq α] [AtomOrder α] in
theorem nth?_tyTT : ∀ {Γ : List Ty} {σ : Ty} (v : Var Γ σ),
    nth? (Γ.map (tyTT (α := α))) v.idx = some (tyTT σ)
  | _, _, .here => rfl
  | _, _, .there v => nth?_tyTT v

/-- **The translation type checks.** -/
theorem infer_trTC (Δ : List (Kind α)) : ∀ {Γ : List Ty} {σ : Ty} (t : Tm Γ σ),
    infer fuel Δ (Γ.map tyTT) (trTC t) = some (tyTT σ)
  | _, _, .var v => nth?_tyTT v
  | _, _, @Tm.lam _ a _ b => infer_lam ((good_tyTT a).kind Δ) (infer_trTC Δ b)
  | _, _, @Tm.app _ a b s u =>
      infer_app (infer_trTC Δ s) (infer_trTC Δ u) ((good_tyTT a).arr (good_tyTT b)).nf
  | _, _, .zero => infer_zeroC Δ _
  | _, _, .succ => infer_succC Δ _
  | Γ, _, .nrec r => infer_recC (good_tyTT r) Δ (Γ.map tyTT)
  | _, _, .tzero => infer_tzeroC Δ _
  | _, _, .tsucc => infer_tsuccC Δ _
  | _, _, .tlim => infer_tlimC Δ _
  | Γ, _, .fold r => infer_foldC (good_tyTT r) Δ (Γ.map tyTT)

end Typing

end BusyLean.Indep.TT
