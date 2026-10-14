import BusyLean.Independent.TreeTyped
import BusyLean.Independent.SystemTLtLadder

/-!
# Rung 3 < rung 4: the Hardy hierarchy at `ε₀` < the self-reflected ladder

The ordinal rung is the value of the `TT` program `epsProgram`
(`eval_epsProgram`). Its Church-style translation is a ladder program of depth
at most `1000` (`cdepth_epsProgramC`; it is `56`) that type checks at type `nat` and reduces to the
Church numeral of `Feps (Feps 42)` under any oracle. So every `ladderMax` with a
budget of at least `1000` exceeds the ordinal rung, and `F4 42 ≥ 1067`.

The comparison is a simulation: impredicative Church encodings of Brouwer trees
carry out the transfinite recursion that defines the hierarchy.
-/

namespace BusyLean.Indep

open BusyLean.FL
open BusyLean.Indep.TT
open BusyLean.Indep.Emb (IsFC IsF cdepth isFC_errC isFC_recC isF_tyT mem_ctmsUpTo)
open BusyLean.Indep.Ladder (fvalue ladderUpTo ladderMax stage listMax)

theorem isF_tyTT {α : Type} : ∀ σ : TT.Ty, IsF (tyTT σ : FL.Ty α)
  | .nat => ⟨rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  | .tree => by
      show IsF (treeTyC : FL.Ty α)
      simp only [treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, and_self]
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

/-! ## Depth of the compiled program -/

/-- The depth of `tyTT a`. -/
def tdTT : TT.Ty → Nat
  | .nat => 5
  | .tree => 11
  | .arr a b => max (tdTT a) (tdTT b) + 1

theorem tdepth_tyTT {α : Type} : ∀ a : TT.Ty, Emb.tdepth (tyTT a : FL.Ty α) = tdTT a
  | .nat => rfl
  | .tree => rfl
  | .arr a b => by
      show max (Emb.tdepth (tyTT a : FL.Ty α)) (Emb.tdepth (tyTT b : FL.Ty α)) + 1 = _
      rw [tdepth_tyTT a, tdepth_tyTT b]; rfl

theorem cdepth_foldC {α : Type} (R : FL.Ty α) : cdepth (foldC R) ≤ Emb.tdepth R + 15 := by
  simp only [cdepth, foldC, app3C, treeTyC, treeBody, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
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

theorem cdTT_epsProgram : cdTT epsProgram ≤ 1000 := by decide +kernel

theorem cdepth_epsProgramC (m : Nat) : cdepth (trTC epsProgram : CTm (Atom m)) ≤ 1000 :=
  Nat.le_trans (cdepth_trTC_le epsProgram) cdTT_epsProgram

/-- Every ladder maximum with budget `≥ 1000` exceeds the ordinal rung, whatever the oracle. -/
theorem contender_3_lt_ladderMax (g : Nat → Nat) {m : Nat} (hm : 1000 ≤ m) :
    contender_3 < ladderMax g m := by
  have hmem : (trTC epsProgram : CTm (Atom m)) ∈ ladderUpTo m :=
    mem_ctmsUpTo _ _ (isFC_trTC epsProgram) (Nat.le_trans (cdepth_epsProgramC m) hm)
  have hty : infer m [] [] (trTC epsProgram : CTm (Atom m)) = some FL.Ty.nat :=
    infer_trTC (fuel := m) [] epsProgram
  have hsteps : F.Steps g (erase (trTC epsProgram : CTm (Atom m))) (F.Tm.num (Feps (Feps 42))) := by
    rw [erase_trTC]
    have h := utrT_steps (f := g) epsProgram
    rw [eval_epsProgram] at h
    exact h
  have hv := fvalue_eq (ℓ := m) hty hsteps
  have hle := le_listMax (fvalue m g m) hmem
  rw [hv] at hle
  unfold contender_3 ladderMax
  generalize listMax (fvalue m g m) (ladderUpTo m) = L at hle ⊢
  generalize Feps (Feps 42) = V at hle ⊢
  omega

/-- **Rung 3 < rung 4**: the ordinal rung < the self-reflected ladder. -/
theorem contender_3_lt_contender_4 : contender_3 < contender_4 := by
  have h42 := F4_42_ge
  have h := contender_3_lt_ladderMax (stage (F4 42)) (m := F4 42)
    (by generalize F4 42 = M at h42; omega)
  have e : contender_4 = ladderMax (stage (F4 42)) (F4 42) := F4_eq (F4 42)
  rw [e]
  exact h

end BusyLean.Indep
