import BusyLean.Independent.TreeTyped
import BusyLean.Independent.TreeDepth
import BusyLean.Independent.SystemTLtLadder
import BusyLean.Independent.OmegaPkg

/-!
# Rung 3 < rung 4: the Hardy hierarchy at `ψ_0(Ω_ω)` < the self-building transfinite ladder

The ordinal rung is computed by one ladder program, `rungProgram`: the
Church-style translation of the `TT` shell `omegaProgram = λθ. H_{lim θ}(H_{lim θ}(42))`
applied to `Omega.thetaF`, which computes Buchholz's family `K ↦ ψ_0(ε_{Ω_{K+2}+1})`
uniformly in the level with impredicative existential packages
(`OmegaPkg.lean`). The program has depth at most `501`, type checks at type
`nat` (`infer_rungProgram`), and reduces to the Church numeral of `F3 (F3 42)`
under any oracle (`steps_rungProgram`). So every `ladderMax` with a budget of at
least `1000` exceeds the ordinal rung, and `F4 42 ≥ 1067`.

The comparison is a simulation: impredicative Church encodings of Brouwer trees
and of Buchholz's trees of every level carry out the transfinite recursion
that defines the collapse and the hierarchy.
-/

namespace BusyLean.Indep

open BusyLean.FL
open BusyLean.Indep.TT
open BusyLean.Indep.Emb (IsFC IsF cdepth isFC_errC isFC_recC isF_tyT mem_ctmsUpTo)
open BusyLean.Indep.Ladder (fvalue ladderUpTo ladderMax listMax)

theorem isF_levShape {α : Type} {D : FL.Ty α} (hD : IsF D) : IsF (levShape D) := by
  simp only [levShape, levBody, tPD, tL, tXX, tX, IsF, FL.Ty.nat, hD, and_self]

theorem isF_domC {α : Type} : ∀ m, IsF (domC m : FL.Ty α)
  | 0 => ⟨rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  | m + 1 => isF_levShape (isF_domC m)

theorem isF_levC {α : Type} (m : Nat) : IsF (levC m : FL.Ty α) := isF_levShape (isF_domC m)

theorem isFC_lfoldC {α : Type} {D R : FL.Ty α} (hD : IsF D) (hR : IsF R) : IsFC (lfoldC D R) := by
  have h := isF_levShape hD
  simp only [IsFC, lfoldC, app4C, app3C, IsF, FL.Ty.nat, hD, hR, h, and_self]

theorem isF_tyTT {α : Type} : ∀ σ : TT.Ty, IsF (tyTT σ : FL.Ty α)
  | .nat => ⟨rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  | .tree => by
      show IsF (treeTyC : FL.Ty α)
      simp only [treeTyC, treeBody, tL, tXX, tX, IsF, FL.Ty.nat, and_self]
  | .lev m => isF_levC m
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
  | _, _, .lzero m => by
      have h := isF_domC (α := α) m
      show IsFC (lzeroC m : CTm α)
      simp only [IsFC, lzeroC, tPD, tL, tXX, tX, IsF, FL.Ty.nat, h, and_self]
  | _, _, .lsucc m => by
      have h := isF_domC (α := α) m
      have h' := isF_levC (α := α) m
      show IsFC (lsuccC m : CTm α)
      simp only [IsFC, lsuccC, app4C, app3C, tPD, tL, tXX, tX, IsF, FL.Ty.nat, h, h', and_self]
  | _, _, .llim m => by
      have h := isF_domC (α := α) m
      have h' := isF_levC (α := α) m
      show IsFC (llimC m : CTm α)
      simp only [IsFC, llimC, app4C, app3C, tPD, tL, tXX, tX, IsF, FL.Ty.nat, h, h', and_self]
  | _, _, .lsup m => by
      have h := isF_levC (α := α) m
      have h' := isF_levC (α := α) (m + 1)
      show IsFC (lsupC m : CTm α)
      simp only [IsFC, lsupC, app4C, app3C, tPD, tL, tXX, tX, IsF, FL.Ty.nat, h, h', and_self]
  | _, _, .lfold0 r => isFC_lfoldC (isF_domC 0) (isF_tyTT r)
  | _, _, .lfoldS m r => isFC_lfoldC (isF_levC m) (isF_tyTT r)

/-! ## Depth of the compiled program -/

theorem tdepth_levShape {α : Type} {D : FL.Ty α} (h : 5 ≤ Emb.tdepth D) :
    Emb.tdepth (levShape D) = Emb.tdepth D + 8 := by
  simp only [levShape, levBody, tPD, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
  omega

theorem tdepth_domC {α : Type} : ∀ m, Emb.tdepth (domC m : FL.Ty α) = 8 * m + 5
  | 0 => rfl
  | m + 1 => by
      show Emb.tdepth (levShape (domC m)) = _
      rw [tdepth_levShape (by rw [tdepth_domC m]; omega), tdepth_domC m]
      omega

theorem tdepth_levC {α : Type} (m : Nat) : Emb.tdepth (levC m : FL.Ty α) = 8 * m + 13 := by
  show Emb.tdepth (levShape (domC m)) = _
  rw [tdepth_levShape (by rw [tdepth_domC m]; omega), tdepth_domC m]

theorem tdepth_tyTT {α : Type} : ∀ a : TT.Ty, Emb.tdepth (tyTT a : FL.Ty α) = tdTT a
  | .nat => rfl
  | .tree => rfl
  | .lev m => tdepth_levC m
  | .arr a b => by
      show max (Emb.tdepth (tyTT a : FL.Ty α)) (Emb.tdepth (tyTT b : FL.Ty α)) + 1 = _
      rw [tdepth_tyTT a, tdepth_tyTT b]; rfl

theorem cdepth_foldC {α : Type} (R : FL.Ty α) : cdepth (foldC R) ≤ Emb.tdepth R + 15 := by
  simp only [cdepth, foldC, app3C, treeTyC, treeBody, tL, tXX, tX, Emb.tdepth, Emb.tdepth_nat]
  omega

theorem max_le_max' {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_max_left c d), Nat.le_trans h2 (Nat.le_max_right c d)⟩

theorem max_add_le_iff (a b n c : Nat) : max a b + n ≤ c ↔ a + n ≤ c ∧ b + n ≤ c := by
  constructor
  · intro h; exact ⟨Nat.le_trans (Nat.add_le_add_right (Nat.le_max_left a b) n) h,
      Nat.le_trans (Nat.add_le_add_right (Nat.le_max_right a b) n) h⟩
  · intro ⟨h1, h2⟩
    rcases Nat.le_total a b with hab | hab
    · rw [Nat.max_eq_right hab]; exact h2
    · rw [Nat.max_eq_left hab]; exact h1

theorem cdepth_lfoldC {α : Type} (D R : FL.Ty α) (hD : 5 ≤ Emb.tdepth D) :
    cdepth (lfoldC D R) ≤ max (Emb.tdepth D) (Emb.tdepth R) + 30 := by
  have hl := tdepth_levShape hD
  simp only [cdepth, lfoldC, app4C, app3C, Emb.tdepth, Emb.tdepth_nat, hl, Nat.add_assoc, max_add_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem cdepth_lzeroC {α : Type} (m : Nat) : cdepth (lzeroC m : CTm α) ≤ 8 * m + 25 := by
  have h := tdepth_domC (α := α) m
  simp only [cdepth, lzeroC, Emb.tdepth, Emb.tdepth_nat, h, Nat.add_assoc, max_add_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem cdepth_lsuccC {α : Type} (m : Nat) : cdepth (lsuccC m : CTm α) ≤ 8 * m + 35 := by
  have h := tdepth_domC (α := α) m
  have h' := tdepth_levC (α := α) m
  simp only [cdepth, lsuccC, app4C, app3C, Emb.tdepth, Emb.tdepth_nat, h, h', Nat.add_assoc, max_add_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem cdepth_llimC {α : Type} (m : Nat) : cdepth (llimC m : CTm α) ≤ 8 * m + 45 := by
  have h := tdepth_domC (α := α) m
  have h' := tdepth_levC (α := α) m
  simp only [cdepth, llimC, app4C, app3C, Emb.tdepth, Emb.tdepth_nat, h, h', Nat.add_assoc, max_add_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem cdepth_lsupC {α : Type} (m : Nat) : cdepth (lsupC m : CTm α) ≤ 8 * m + 55 := by
  have h := tdepth_levC (α := α) m
  have h' := tdepth_levC (α := α) (m + 1)
  simp only [cdepth, lsupC, app4C, app3C, Emb.tdepth, Emb.tdepth_nat, h, h', Nat.add_assoc, max_add_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem cdepth_trTC_le {α : Type} : ∀ {Γ : List TT.Ty} {σ : TT.Ty} (t : TT.Tm Γ σ),
    cdepth (trTC t : CTm α) ≤ cdTT t
  | _, _, .var _ => Nat.le_refl _
  | _, _, @TT.Tm.lam _ a _ b => by
      have := cdepth_trTC_le (α := α) b
      show max (Emb.tdepth (tyTT a : FL.Ty α)) (cdepth (trTC b : CTm α)) + 1 ≤
        max (tdTT a) (cdTT b) + 1
      rw [tdepth_tyTT]
      exact Nat.succ_le_succ (max_le_max' (Nat.le_refl _) this)
  | _, _, .app s u => by
      have := cdepth_trTC_le (α := α) s
      have := cdepth_trTC_le (α := α) u
      show max (cdepth (trTC s : CTm α)) (cdepth (trTC u : CTm α)) + 1 ≤
        max (cdTT s) (cdTT u) + 1
      exact Nat.succ_le_succ (max_le_max' ‹_› ‹_›)
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
  | _, _, .lzero m => cdepth_lzeroC m
  | _, _, .lsucc m => cdepth_lsuccC m
  | _, _, .llim m => cdepth_llimC m
  | _, _, .lsup m => cdepth_lsupC m
  | _, _, .lfold0 r => by
      have := cdepth_lfoldC (FL.Ty.nat : FL.Ty α) (tyTT r) (by rw [Emb.tdepth_nat]; exact Nat.le_refl 5)
      rw [tdepth_tyTT, Emb.tdepth_nat] at this
      show cdepth (lfoldC FL.Ty.nat (tyTT r) : CTm α) ≤ tdTT r + 35
      omega
  | _, _, .lfoldS m r => by
      have := cdepth_lfoldC (levC m : FL.Ty α) (tyTT r) (by rw [tdepth_levC]; omega)
      rw [tdepth_tyTT, tdepth_levC] at this
      show cdepth (lfoldC (levC m) (tyTT r) : CTm α) ≤ tdTT r + 8 * m + 45
      omega

theorem cdepth_omegaProgramC (m : Nat) : cdepth (trTC omegaProgram : CTm (Atom m)) ≤ 500 :=
  Nat.le_trans (cdepth_trTC_le omegaProgram) cdTT_omegaProgram

/-- The rung as one ladder program: the tree-language shell `λθ. H_{lim θ}(H_{lim θ}(42))`
applied to Buchholz's family, built uniformly in the level by `Omega.thetaF`. -/
def rungProgram (m : Nat) : CTm (Atom m) := .app (trTC omegaProgram) (SF.embC Omega.thetaF)

theorem cdepth_rungProgram (m : Nat) : cdepth (rungProgram m) ≤ 501 := by
  show max (cdepth (trTC omegaProgram : CTm (Atom m))) (cdepth (SF.embC Omega.thetaF : CTm (Atom m)))
    + 1 ≤ 501
  rw [SF.cdepth_embC]
  have h1 := cdepth_omegaProgramC m
  have h2 := Omega.cdepth_thetaF
  generalize cdepth (trTC omegaProgram : CTm (Atom m)) = a at h1 ⊢
  generalize SF.cdepthF Omega.thetaF = b at h2 ⊢
  omega

theorem infer_rungProgram (m : Nat) : infer m [] [] (rungProgram m) = some FL.Ty.nat := by
  have ht := infer_trTC (fuel := m) (α := Atom m) [] omegaProgram
  have hu : infer m [] [] (SF.embC Omega.thetaF : CTm (Atom m)) =
      some (tyTT (.arr .nat .tree)) := SF.infer_embC Omega.check_thetaF m [] []
  exact Emb.infer_app ht hu ((good_tyTT (.arr .nat .tree)).arr (good_tyTT .nat)).nf

/-- The rung program reduces to the numeral of the ordinal rung, under any oracle. -/
theorem steps_rungProgram (g : Nat → Nat) (m : Nat) :
    F.Steps g (erase (rungProgram m)) (F.Tm.num (F3 (F3 42))) := by
  show F.Steps g (F.Tm.app (erase (trTC omegaProgram : CTm (Atom m)))
    (erase (SF.embC Omega.thetaF : CTm (Atom m)))) _
  rw [erase_trTC, SF.erase_embC]
  have hP := Omega.rel_utrT0 (f := g) omegaProgram
  have h := hP (SF.eraseF Omega.thetaF) (fun K => Buch.theta (K + 1)) Omega.rel_thetaF
  rw [eval_omegaProgram_rung] at h
  exact h

/-- Every ladder maximum with budget `≥ 1000` exceeds the ordinal rung, whatever the oracle. -/
theorem contender_3_lt_ladderMax (g : Nat → Nat) {m : Nat} (hm : 1000 ≤ m) :
    contender_3 < ladderMax g m := by
  have hmem : rungProgram m ∈ ladderUpTo m :=
    mem_ctmsUpTo _ _ ⟨isFC_trTC omegaProgram, SF.isFC_embC Omega.thetaF⟩
      (Nat.le_trans (cdepth_rungProgram m) (Nat.le_trans (by decide) hm))
  have hv := fvalue_eq (ℓ := m) (infer_rungProgram m) (steps_rungProgram g m)
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
