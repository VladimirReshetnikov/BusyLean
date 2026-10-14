import BusyLean.Independent.TreeTyped
import BusyLean.Independent.SystemTLtLadder

/-!
# Rung 3 < rung 4: the Hardy hierarchy at `θ` < the self-building transfinite ladder

The ordinal rung is the value of the `TT` program `bhProgram`
(`eval_bhProgram`). Its Church-style translation is a ladder program of depth
at most `1000` (`cdepth_bhProgramC`; it is `57`) that type checks at type `nat`
and reduces to the Church numeral of `F3 (F3 42)` under any oracle. So every
`ladderMax` with a budget of at least `1000` exceeds the ordinal rung, and
`F4 42 ≥ 1067`.

The comparison is a simulation: impredicative Church encodings of Brouwer trees
and `Ω`-trees carry out the transfinite recursion that defines the collapse
and the hierarchy.
-/

namespace BusyLean.Indep

open BusyLean.FL
open BusyLean.Indep.TT
open BusyLean.Indep.Emb (IsFC IsF cdepth isFC_errC isFC_recC isF_tyT mem_ctmsUpTo)
open BusyLean.Indep.Ladder (fvalue ladderUpTo ladderMax listMax)

theorem isF_tyTT {α : Type} : ∀ σ : TT.Ty, IsF (tyTT σ : FL.Ty α)
  | .nat => ⟨rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  | .tree => by
      show IsF (treeTyC : FL.Ty α)
      simp only [treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, and_self]
  | .otree => by
      show IsF (otreeTyC : FL.Ty α)
      simp only [otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, and_self]
  | .arr a b => ⟨isF_tyTT a, isF_tyTT b⟩

theorem isFC_trTC {α : Type} : ∀ {Γ : List TT.Ty} {σ : TT.Ty} (t : TT.Tm Γ σ), IsFC (trTC t : CTm α)
  | _, _, .var _ => trivial
  | _, _, @TT.Tm.lam _ a _ b => ⟨isF_tyTT a, isFC_trTC b⟩
  | _, _, .app s u => ⟨isFC_trTC s, isFC_trTC u⟩
  | _, _, .zero => isFC_errC .nat
  | _, _, .succ => by
      show IsFC (Emb.succC : CTm α)
      simp only [IsFC, Emb.succC, IsF, FL.Ty.nat, and_self]
  | _, _, .nrec r => isFC_recC (isF_tyTT r)
  | _, _, .tzero => by
      show IsFC (tzeroC : CTm α)
      simp only [IsFC, tzeroC, IsF, FL.Ty.nat, and_self]
  | _, _, .tsucc => by
      show IsFC (tsuccC : CTm α)
      simp only [IsFC, tsuccC, app3C, treeTyC, IsF, FL.Ty.nat, and_self]
  | _, _, .tlim => by
      show IsFC (tlimC : CTm α)
      simp only [IsFC, tlimC, app3C, treeTyC, IsF, FL.Ty.nat, and_self]
  | _, _, .fold r => by
      have h := isF_tyTT (α := α) r
      show IsFC (foldC (tyTT r) : CTm α)
      simp only [IsFC, foldC, app3C, treeTyC, IsF, FL.Ty.nat, h, and_self]
  | _, _, .ozero => by
      show IsFC (ozeroC : CTm α)
      simp only [IsFC, ozeroC, tP, treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, and_self]
  | _, _, .osucc => by
      show IsFC (osuccC : CTm α)
      simp only [IsFC, osuccC, app4C, app3C, otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, and_self]
  | _, _, .olim => by
      show IsFC (olimC : CTm α)
      simp only [IsFC, olimC, app4C, app3C, otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, and_self]
  | _, _, .osup => by
      show IsFC (osupC : CTm α)
      simp only [IsFC, osupC, app4C, app3C, otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, and_self]
  | _, _, .ofold r => by
      have h := isF_tyTT (α := α) r
      show IsFC (ofoldC (tyTT r) : CTm α)
      simp only [IsFC, ofoldC, app4C, app3C, otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, h, and_self]

/-! ## Depth of the compiled program -/

/-- The depth of `tyTT a`. -/
def tdTT : TT.Ty → Nat
  | .nat => 5
  | .tree => 11
  | .otree => 18
  | .arr a b => max (tdTT a) (tdTT b) + 1

theorem tdepth_tyTT {α : Type} : ∀ a : TT.Ty, Emb.tdepth (tyTT a : FL.Ty α) = tdTT a
  | .nat => rfl
  | .tree => rfl
  | .otree => rfl
  | .arr a b => by
      show max (Emb.tdepth (tyTT a : FL.Ty α)) (Emb.tdepth (tyTT b : FL.Ty α)) + 1 = _
      rw [tdepth_tyTT a, tdepth_tyTT b]; rfl

theorem cdepth_foldC {α : Type} (R : FL.Ty α) : cdepth (foldC R) ≤ Emb.tdepth R + 15 := by
  simp only [cdepth, foldC, app3C, treeTyC, treeBody, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
  omega

theorem cdepth_ofoldC {α : Type} (R : FL.Ty α) : cdepth (ofoldC R) ≤ Emb.tdepth R + 25 := by
  simp only [cdepth, ofoldC, app4C, app3C, otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
  omega

theorem cdepth_ozeroC {α : Type} : cdepth (ozeroC : CTm α) ≤ 20 := by
  simp only [cdepth, ozeroC, tP, treeTyC, treeBody, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
  omega

theorem cdepth_osuccC {α : Type} : cdepth (osuccC : CTm α) ≤ 25 := by
  simp only [cdepth, osuccC, app4C, app3C, otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
  omega

theorem cdepth_olimC {α : Type} : cdepth (olimC : CTm α) ≤ 25 := by
  simp only [cdepth, olimC, app4C, app3C, otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
  omega

theorem cdepth_osupC {α : Type} : cdepth (osupC : CTm α) ≤ 25 := by
  simp only [cdepth, osupC, app4C, app3C, otreeTyC, otreeBody, tP, treeTyC, treeBody, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
  omega

/-- A bound on the depth of `trTC t`, computed on the `TT` term. -/
def cdTT : {Γ : List TT.Ty} → {σ : TT.Ty} → TT.Tm Γ σ → Nat
  | _, _, .var v => v.idx + 2
  | _, _, @TT.Tm.lam _ a _ b => max (tdTT a) (cdTT b) + 1
  | _, _, .app s u => max (cdTT s) (cdTT u) + 1
  | _, _, .zero => 5
  | _, _, .succ => 12
  | _, _, .nrec r => tdTT r + 45
  | _, _, .tzero => 20
  | _, _, .tsucc => 30
  | _, _, .tlim => 30
  | _, _, .fold r => tdTT r + 15
  | _, _, .ozero => 20
  | _, _, .osucc => 25
  | _, _, .olim => 25
  | _, _, .osup => 25
  | _, _, .ofold r => tdTT r + 25

theorem cdepth_trTC_le {α : Type} : ∀ {Γ : List TT.Ty} {σ : TT.Ty} (t : TT.Tm Γ σ),
    cdepth (trTC t : CTm α) ≤ cdTT t
  | _, _, .var _ => Nat.le_refl _
  | _, _, @TT.Tm.lam _ a _ b => by
      have := cdepth_trTC_le (α := α) b
      show max (Emb.tdepth (tyTT a : FL.Ty α)) (cdepth (trTC b : CTm α)) + 1 ≤ _
      rw [tdepth_tyTT]; simp only [cdTT]; omega
  | _, _, .app s u => by
      have := cdepth_trTC_le (α := α) s
      have := cdepth_trTC_le (α := α) u
      show max (cdepth (trTC s : CTm α)) (cdepth (trTC u : CTm α)) + 1 ≤ _
      simp only [cdTT]; omega
  | _, _, .zero => by show 5 ≤ 5; omega
  | _, _, .succ => by show 12 ≤ 12; omega
  | _, _, .nrec r => by
      have := Emb.cdepth_recC (tyTT r : FL.Ty α)
      rw [tdepth_tyTT] at this
      exact this
  | _, _, .tzero => Nat.le_of_ble_eq_true rfl
  | _, _, .tsucc => Nat.le_of_ble_eq_true rfl
  | _, _, .tlim => Nat.le_of_ble_eq_true rfl
  | _, _, .fold r => by
      have := cdepth_foldC (tyTT r : FL.Ty α)
      rw [tdepth_tyTT] at this
      exact this
  | _, _, .ozero => cdepth_ozeroC
  | _, _, .osucc => cdepth_osuccC
  | _, _, .olim => cdepth_olimC
  | _, _, .osup => cdepth_osupC
  | _, _, .ofold r => by
      have := cdepth_ofoldC (tyTT r : FL.Ty α)
      rw [tdepth_tyTT] at this
      exact this

theorem cdTT_bhProgram : cdTT bhProgram ≤ 1000 := by decide +kernel

theorem cdepth_bhProgramC (m : Nat) : cdepth (trTC bhProgram : CTm (Atom m)) ≤ 1000 :=
  Nat.le_trans (cdepth_trTC_le bhProgram) cdTT_bhProgram

/-- Every ladder maximum with budget `≥ 1000` exceeds the ordinal rung, whatever the oracle. -/
theorem contender_3_lt_ladderMax (g : Nat → Nat) {m : Nat} (hm : 1000 ≤ m) :
    contender_3 < ladderMax g m := by
  have hmem : (trTC bhProgram : CTm (Atom m)) ∈ ladderUpTo m :=
    mem_ctmsUpTo _ _ (isFC_trTC bhProgram) (Nat.le_trans (cdepth_bhProgramC m) hm)
  have hty : infer m [] [] (trTC bhProgram : CTm (Atom m)) = some FL.Ty.nat :=
    infer_trTC (fuel := m) [] bhProgram
  have hsteps : F.Steps g (erase (trTC bhProgram : CTm (Atom m))) (F.Tm.num (F3 (F3 42))) := by
    rw [erase_trTC]
    have h := utrT_steps (f := g) bhProgram
    rw [eval_bhProgram] at h
    exact h
  have hv := fvalue_eq (ℓ := m) hty hsteps
  have hle := le_listMax (fvalue m g m) hmem
  rw [hv] at hle
  unfold contender_3 ladderMax
  generalize listMax (fvalue m g m) (ladderUpTo m) = L at hle ⊢
  generalize F3 (F3 42) = V at hle ⊢
  omega

/-- **Rung 3 < rung 4**: the ordinal rung < the self-building transfinite ladder. -/
theorem contender_3_lt_contender_4 : contender_3 < contender_4 := by
  have h42 := F4_42_ge
  have h := contender_3_lt_ladderMax (orc4 (F4 42)) (m := F4 42)
    (by generalize F4 42 = M at h42; omega)
  have e : contender_4 = ladderMax (orc4 (F4 42)) (F4 42) := F4_eq (F4 42)
  rw [e]
  exact h

end BusyLean.Indep
