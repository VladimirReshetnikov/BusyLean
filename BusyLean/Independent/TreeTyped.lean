import BusyLean.Independent.TreeEmbedding
import BusyLean.Independent.TTyped

/-!
# `TT` as Church-style ladder programs

The tree type is `∀X. X → (X → X) → ((nat → X) → X) → X`, and the type of
level trees is `∀X. X → (X → X) → ((nat → X) → X) → (nat → (D → X) → X) → X`, where `D`
is `nat` at level `0` and the type of the previous level otherwise. `trTC` translates
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

theorem tstep_arr_none {A B : FL.Ty α} (hA : tstep A = none) (hB : tstep B = none) :
    tstep (FL.Ty.arr A B) = none := by
  show (match tstep A with
    | some A' => some (FL.Ty.arr A' B)
    | none => (tstep B).map (FL.Ty.arr A)) = none
  rw [hA, hB]; rfl

theorem kind_arr {Δ : List (Kind α)} {A B : FL.Ty α} (hA : inferKind Δ A = some .star)
    (hB : inferKind Δ B = some .star) : inferKind Δ (FL.Ty.arr A B) = some .star := by
  show arrK (inferKind Δ A) (inferKind Δ B) = _
  rw [hA, hB]; rfl

/-- The handler type of `sup` nodes branching over `D`: `nat → (D → X) → X`. -/
abbrev tPD (D : FL.Ty α) : FL.Ty α := .arr FL.Ty.nat (.arr (.arr D tX) tX)

abbrev levBody (D : FL.Ty α) : FL.Ty α := .arr tX (.arr tXX (.arr tL (.arr (tPD D) tX)))

/-- `∀X. X → (X → X) → ((nat → X) → X) → (nat → (D → X) → X) → X`. -/
def levShape (D : FL.Ty α) : FL.Ty α := .all .star (levBody D)

/-- The branching types: `nat` at level `0`, level `m` trees at level `m + 1`. -/
def domC : Nat → FL.Ty α
  | 0 => FL.Ty.nat
  | m + 1 => levShape (domC m)

/-- The Church type of trees of level `m`. -/
def levC (m : Nat) : FL.Ty α := levShape (domC m)

theorem good_levShape {D : FL.Ty α} (hD : Good D) : Good (levShape D) where
  ren ξ := by
    show FL.Ty.all .star (FL.Ty.arr (Ty.tren _ tX) (FL.Ty.arr (Ty.tren _ tXX) (FL.Ty.arr (Ty.tren _ tL)
      (FL.Ty.arr (FL.Ty.arr (Ty.tren _ FL.Ty.nat) (FL.Ty.arr (FL.Ty.arr (Ty.tren _ D) (Ty.tren _ tX))
        (Ty.tren _ tX))) (Ty.tren _ tX))))) = _
    rw [hD.ren]; rfl
  subst σ := by
    show FL.Ty.all .star (FL.Ty.arr (Ty.tsubst _ tX) (FL.Ty.arr (Ty.tsubst _ tXX) (FL.Ty.arr (Ty.tsubst _ tL)
      (FL.Ty.arr (FL.Ty.arr (Ty.tsubst _ FL.Ty.nat) (FL.Ty.arr (FL.Ty.arr (Ty.tsubst _ D) (Ty.tsubst _ tX))
        (Ty.tsubst _ tX))) (Ty.tsubst _ tX))))) = _
    rw [hD.subst]; rfl
  nf := by
    show (tstep (levBody D)).map (FL.Ty.all .star) = none
    have hP : tstep (tPD D) = none :=
      tstep_arr_none good_nat.nf (tstep_arr_none (tstep_arr_none hD.nf rfl) rfl)
    rw [tstep_arr_none rfl (tstep_arr_none rfl (tstep_arr_none rfl (tstep_arr_none hP rfl)))]
    rfl
  kind Δ := by
    show starK (inferKind (.star :: Δ) (levBody D)) = _
    have hP : inferKind (.star :: Δ) (tPD D) = some .star :=
      kind_arr (good_nat.kind _) (kind_arr (kind_arr (hD.kind _) rfl) rfl)
    rw [kind_arr rfl (kind_arr rfl (kind_arr rfl (kind_arr hP rfl)))]
    rfl

theorem good_domC : ∀ m, Good (domC m : FL.Ty α)
  | 0 => good_nat
  | m + 1 => good_levShape (good_domC m)

theorem good_levC (m : Nat) : Good (levC m : FL.Ty α) := good_levShape (good_domC m)

def tyTT : Ty → FL.Ty α
  | .nat => FL.Ty.nat
  | .tree => treeTyC
  | .lev m => levC m
  | .arr a b => .arr (tyTT a) (tyTT b)

theorem good_tyTT : ∀ σ : Ty, Good (tyTT σ : FL.Ty α)
  | .nat => good_nat
  | .tree => good_treeTyC
  | .lev m => good_levC m
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

def app4C (u z s l p : CTm α) : CTm α := .app (app3C u z s l) p

def lzeroC (m : Nat) : CTm α :=
  .tlam .star (.lam tX (.lam tXX (.lam tL (.lam (tPD (domC m)) (.var 3)))))

def lsuccC (m : Nat) : CTm α :=
  .lam (levC m) (.tlam .star (.lam tX (.lam tXX (.lam tL (.lam (tPD (domC m))
    (.app (.var 2) (app4C (.tapp (.var 4) tX) (.var 3) (.var 2) (.var 1) (.var 0))))))))

def llimC (m : Nat) : CTm α :=
  .lam (.arr FL.Ty.nat (levC m)) (.tlam .star (.lam tX (.lam tXX (.lam tL (.lam (tPD (domC m))
    (.app (.var 1) (.lam FL.Ty.nat
      (app4C (.tapp (.app (.var 5) (.var 0)) tX) (.var 4) (.var 3) (.var 2) (.var 1)))))))))

def lsupC (m : Nat) : CTm α :=
  .lam FL.Ty.nat (.lam (.arr (levC m) (levC (m + 1))) (.tlam .star (.lam tX (.lam tXX (.lam tL
    (.lam (tPD (levC m)) (.app (.app (.var 0) (.var 5)) (.lam (levC m)
      (app4C (.tapp (.app (.var 5) (.var 0)) tX) (.var 4) (.var 3) (.var 2) (.var 1))))))))))

def lsup0C : CTm α :=
  .lam FL.Ty.nat (.lam (.arr FL.Ty.nat (levC 0)) (.tlam .star (.lam tX (.lam tXX (.lam tL
    (.lam (tPD FL.Ty.nat) (.app (.app (.var 0) (.var 5)) (.lam FL.Ty.nat
      (app4C (.tapp (.app (.var 5) (.var 0)) tX) (.var 4) (.var 3) (.var 2) (.var 1))))))))))

def lfoldC (D R : FL.Ty α) : CTm α :=
  .lam R (.lam (.arr R R) (.lam (.arr (.arr FL.Ty.nat R) R)
    (.lam (.arr FL.Ty.nat (.arr (.arr D R) R)) (.lam (levShape D)
      (app4C (.tapp (.var 0) R) (.var 4) (.var 3) (.var 2) (.var 1))))))

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
  | _, _, .lzero m => lzeroC m
  | _, _, .lsucc m => lsuccC m
  | _, _, .llim m => llimC m
  | _, _, .lsup m => lsupC m
  | _, _, .lsup0 => lsup0C
  | _, _, .lfold0 r => lfoldC FL.Ty.nat (tyTT r)
  | _, _, .lfoldS m r => lfoldC (levC m) (tyTT r)

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
  | _, _, .lzero _ => rfl
  | _, _, .lsucc _ => rfl
  | _, _, .llim _ => rfl
  | _, _, .lsup _ => rfl
  | _, _, .lsup0 => rfl
  | _, _, .lfold0 _ => rfl
  | _, _, .lfoldS _ _ => rfl

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

theorem kind_tPD {D : FL.Ty α} (hD : Good D) (Δ : List (Kind α)) :
    inferKind (.star :: Δ) (tPD D) = some .star :=
  kind_arr (good_nat.kind _) (kind_arr (kind_arr (hD.kind _) rfl) rfl)

/-- The body of a level tree type, instantiated at `X`. -/
abbrev levInst (D X : FL.Ty α) : FL.Ty α :=
  .arr X (.arr (.arr X X) (.arr (.arr (.arr FL.Ty.nat X) X) (.arr (.arr FL.Ty.nat (.arr (.arr D X) X)) X)))

theorem inst_levBody {D : FL.Ty α} (hD : Good D) (X : FL.Ty α) :
    FL.Ty.inst (levBody D) X = levInst D X := by
  show FL.Ty.arr (Ty.tsubst _ tX) (FL.Ty.arr (Ty.tsubst _ tXX) (FL.Ty.arr (Ty.tsubst _ tL)
      (FL.Ty.arr (FL.Ty.arr (Ty.tsubst _ FL.Ty.nat) (FL.Ty.arr (FL.Ty.arr (Ty.tsubst _ D) (Ty.tsubst _ tX))
        (Ty.tsubst _ tX))) (Ty.tsubst _ tX)))) = _
  rw [hD.subst]; rfl

theorem nf_levInst {D X : FL.Ty α} (hD : tstep D = none) (hX : tstep X = none) :
    tstep (levInst D X) = none ∧
      tstep (FL.Ty.arr (.arr X X) (.arr (.arr (.arr FL.Ty.nat X) X)
        (.arr (.arr FL.Ty.nat (.arr (.arr D X) X)) X))) = none ∧
      tstep (FL.Ty.arr (.arr (.arr FL.Ty.nat X) X) (.arr (.arr FL.Ty.nat (.arr (.arr D X) X)) X)) =
        none ∧
      tstep (FL.Ty.arr (.arr FL.Ty.nat (.arr (.arr D X) X)) X) = none := by
  have hXX := tstep_arr_none hX hX
  have hL := tstep_arr_none (tstep_arr_none good_nat.nf hX) hX
  have hP := tstep_arr_none good_nat.nf (tstep_arr_none (tstep_arr_none hD hX) hX)
  have h4 := tstep_arr_none hP hX
  have h3 := tstep_arr_none hL h4
  have h2 := tstep_arr_none hXX h3
  exact ⟨tstep_arr_none hX h2, h2, h3, h4⟩

/-- Applying a term of level tree type to a type and four arguments. -/
theorem infer_app4_lev {D X : FL.Ty α} (hD : Good D) (hX : tstep X = none)
    {Δ : List (Kind α)} {Γ : List (FL.Ty α)} {t z s l p : CTm α}
    (ht : infer fuel Δ Γ t = some (levShape D)) (hXk : inferKind Δ X = some .star)
    (hz : infer fuel Δ Γ z = some X) (hs : infer fuel Δ Γ s = some (.arr X X))
    (hl : infer fuel Δ Γ l = some (.arr (.arr FL.Ty.nat X) X))
    (hp : infer fuel Δ Γ p = some (.arr FL.Ty.nat (.arr (.arr D X) X))) :
    infer fuel Δ Γ (app4C (.tapp t X) z s l p) = some X := by
  have h1 : infer fuel Δ Γ (.tapp t X) = some (levInst D X) := by
    rw [infer_tapp (A := levBody D) ht (good_levShape hD).nf hXk, inst_levBody hD]
  have hn := nf_levInst hD.nf hX
  exact infer_app (infer_app (infer_app (infer_app h1 hz hn.1) hs hn.2.1) hl hn.2.2.1) hp hn.2.2.2

theorem lookup_ren {Γ : List (FL.Ty α)} {A : FL.Ty α} (hA : Good A) {n : Nat}
    (h : nth? Γ n = some A) : nth? (Γ.map (Ty.tren Nat.succ)) n = some A := by
  induction Γ generalizing n with
  | nil => exact nomatch h
  | cons B Γ ih =>
      cases n with
      | zero =>
          have e : B = A := Option.some.inj h
          subst e
          show some (Ty.tren Nat.succ B) = some B
          rw [hA.ren]
      | succ n => exact ih h

theorem infer_lzeroC (m : Nat) (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ (lzeroC m) = some (levC m) :=
  infer_tlam (infer_lam rfl (infer_lam rfl (infer_lam (kind_tL Δ)
    (infer_lam (kind_tPD (good_domC m) Δ) rfl))))

theorem infer_lsuccC (m : Nat) (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ (lsuccC m) = some (.arr (levC m) (levC m)) := by
  refine infer_lam ((good_levC m).kind Δ) (infer_tlam (infer_lam rfl (infer_lam rfl
    (infer_lam (kind_tL Δ) (infer_lam (kind_tPD (good_domC m) Δ) ?_)))))
  refine infer_app (A := tX) rfl ?_ rfl
  exact infer_app4_lev (good_domC m) rfl
    (lookup_ren (Γ := levC m :: Γ) (n := 0) (good_levC (α := α) m) rfl) rfl rfl rfl rfl rfl

theorem infer_llimC (m : Nat) (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ (llimC m) = some (.arr (.arr FL.Ty.nat (levC m)) (levC m)) := by
  have hg := good_nat.arr (good_levC (α := α) m)
  refine infer_lam (hg.kind Δ) (infer_tlam (infer_lam rfl (infer_lam rfl
    (infer_lam (kind_tL Δ) (infer_lam (kind_tPD (good_domC m) Δ) ?_)))))
  refine infer_app (A := .arr FL.Ty.nat tX) rfl ?_ rfl
  refine infer_lam rfl ?_
  have h5 : infer fuel (.star :: Δ)
      (FL.Ty.nat :: tPD (domC m) :: tL :: tXX :: tX ::
        (FL.Ty.arr FL.Ty.nat (levC m) :: Γ).map (Ty.tren Nat.succ))
      (.var 5) = some (.arr FL.Ty.nat (levC m)) :=
    lookup_ren (Γ := FL.Ty.arr FL.Ty.nat (levC m) :: Γ) (n := 0) hg rfl
  exact infer_app4_lev (good_domC m) rfl (infer_app h5 rfl hg.nf) rfl rfl rfl rfl rfl

theorem infer_lsupC (m : Nat) (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ (lsupC m) =
      some (.arr FL.Ty.nat (.arr (.arr (levC m) (levC (m + 1))) (levC (m + 1)))) := by
  have hg := (good_levC m).arr (good_levC (α := α) (m + 1))
  refine infer_lam (good_nat.kind Δ) (infer_lam (hg.kind Δ) (infer_tlam (infer_lam rfl
    (infer_lam rfl (infer_lam (kind_tL Δ) (infer_lam (kind_tPD (good_levC m) Δ) ?_))))))
  have hP : tstep (tPD (levC m) : FL.Ty α) = none :=
    tstep_arr_none good_nat.nf (tstep_arr_none (tstep_arr_none (good_levC m).nf rfl) rfl)
  have h05 : infer fuel (.star :: Δ)
      (tPD (levC m) :: tL :: tXX :: tX ::
        (FL.Ty.arr (levC m) (levC (m + 1)) :: FL.Ty.nat :: Γ).map (Ty.tren Nat.succ))
      (.app (.var 0) (.var 5)) = some (.arr (.arr (levC m) tX) tX) :=
    infer_app rfl (lookup_ren (Γ := FL.Ty.arr (levC m) (levC (m + 1)) :: FL.Ty.nat :: Γ) (n := 1)
      good_nat rfl) hP
  refine infer_app h05 (infer_lam ((good_levC m).kind _) ?_)
    (tstep_arr_none (tstep_arr_none (good_levC m).nf rfl) rfl)
  have h6 : infer fuel (.star :: Δ)
      (levC m :: tPD (levC m) :: tL :: tXX :: tX ::
        (FL.Ty.arr (levC m) (levC (m + 1)) :: FL.Ty.nat :: Γ).map (Ty.tren Nat.succ))
      (.var 5) = some (.arr (levC m) (levC (m + 1))) :=
    lookup_ren (Γ := FL.Ty.arr (levC m) (levC (m + 1)) :: FL.Ty.nat :: Γ) (n := 0) hg rfl
  exact infer_app4_lev (good_levC m) rfl (infer_app h6 rfl hg.nf) rfl rfl rfl rfl rfl

theorem infer_lsup0C (Δ : List (Kind α)) (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ lsup0C =
      some (.arr FL.Ty.nat (.arr (.arr FL.Ty.nat (levC 0)) (levC 0))) := by
  have hg := good_nat.arr (good_levC (α := α) 0)
  refine infer_lam (good_nat.kind Δ) (infer_lam (hg.kind Δ) (infer_tlam (infer_lam rfl
    (infer_lam rfl (infer_lam (kind_tL Δ) (infer_lam (kind_tPD good_nat Δ) ?_))))))
  have hP : tstep (tPD FL.Ty.nat : FL.Ty α) = none :=
    tstep_arr_none good_nat.nf (tstep_arr_none (tstep_arr_none good_nat.nf rfl) rfl)
  have h05 : infer fuel (.star :: Δ)
      (tPD FL.Ty.nat :: tL :: tXX :: tX ::
        (FL.Ty.arr FL.Ty.nat (levC 0) :: FL.Ty.nat :: Γ).map (Ty.tren Nat.succ))
      (.app (.var 0) (.var 5)) = some (.arr (.arr FL.Ty.nat tX) tX) :=
    infer_app rfl (lookup_ren (Γ := FL.Ty.arr FL.Ty.nat (levC 0) :: FL.Ty.nat :: Γ) (n := 1)
      good_nat rfl) hP
  refine infer_app h05 (infer_lam (good_nat.kind _) ?_)
    (tstep_arr_none (tstep_arr_none good_nat.nf rfl) rfl)
  have h6 : infer fuel (.star :: Δ)
      (FL.Ty.nat :: tPD FL.Ty.nat :: tL :: tXX :: tX ::
        (FL.Ty.arr FL.Ty.nat (levC 0) :: FL.Ty.nat :: Γ).map (Ty.tren Nat.succ))
      (.var 5) = some (.arr FL.Ty.nat (levC 0)) :=
    lookup_ren (Γ := FL.Ty.arr FL.Ty.nat (levC 0) :: FL.Ty.nat :: Γ) (n := 0) hg rfl
  exact infer_app4_lev (good_domC 0) rfl (infer_app h6 rfl hg.nf) rfl rfl rfl rfl rfl

theorem infer_lfoldC {D R : FL.Ty α} (hD : Good D) (hR : Good R) (Δ : List (Kind α))
    (Γ : List (FL.Ty α)) :
    infer fuel Δ Γ (lfoldC D R) =
      some (.arr R (.arr (.arr R R) (.arr (.arr (.arr FL.Ty.nat R) R)
        (.arr (.arr FL.Ty.nat (.arr (.arr D R) R)) (.arr (levShape D) R))))) := by
  have hRR : Good (FL.Ty.arr R R) := hR.arr hR
  have hL : Good (FL.Ty.arr (.arr FL.Ty.nat R) R) := (good_nat.arr hR).arr hR
  have hP : Good (FL.Ty.arr FL.Ty.nat (.arr (.arr D R) R)) := good_nat.arr ((hD.arr hR).arr hR)
  refine infer_lam (hR.kind Δ) (infer_lam (hRR.kind Δ) (infer_lam (hL.kind Δ)
    (infer_lam (hP.kind Δ) (infer_lam ((good_levShape hD).kind Δ) ?_))))
  exact infer_app4_lev hD hR.nf rfl (hR.kind Δ) rfl rfl rfl rfl

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
  | _, _, .lzero m => infer_lzeroC m Δ _
  | _, _, .lsucc m => infer_lsuccC m Δ _
  | _, _, .llim m => infer_llimC m Δ _
  | _, _, .lsup m => infer_lsupC m Δ _
  | _, _, .lsup0 => infer_lsup0C Δ _
  | Γ, _, .lfold0 r => infer_lfoldC good_nat (good_tyTT r) Δ (Γ.map tyTT)
  | Γ, _, .lfoldS m r => infer_lfoldC (good_levC m) (good_tyTT r) Δ (Γ.map tyTT)

end Typing

end BusyLean.Indep.TT
