import BusyLean.Independent.TFBSem
import BusyLean.Independent.SystemTLtLadder

/-!
# Rung 3 < rung 4: the Hardy hierarchy at `ψ_0(ε_{Ω_ω+1})` < the self-building transfinite ladder

The ordinal rung is computed by one ladder program, `rungProgram`: the
Fω translation of the `TT` shell `tfbShell = λθ. H_θ(H_θ(42))` applied to
`TFB.thetaW`, which computes the Takeuti–Feferman–Buchholz ordinal
`ψ_0(ε_{Ω_ω+1})` as a Brouwer tree (`TFBProg.lean`). The program has depth
`153`, the verified checker gives it type `nat` at fuel `5` (`check_tfbProgram`),
and it reduces to the Church numeral of `F3 (F3 42)` under any oracle
(`steps_rungProgram`, from `TFB.rel_thetaW`). So every `ladderMax` with a
budget of at least `153` exceeds the ordinal rung, and `F4 42 ≥ 1067`.

The comparison is a simulation: impredicative Church encodings of Brouwer trees,
of Buchholz's trees of every level and of the trees of level `ω`, with
type-level evidence for induction over the levels, carry out the transfinite
recursion that defines the collapse and the hierarchy.
-/

namespace BusyLean.Indep

open BusyLean.FL
open BusyLean.Indep.FW
open BusyLean.Indep.TFB (natW treeW thetaW trTL rel_thetaW)
open BusyLean.Indep.Ladder (fvalue ladderUpTo ladderMax listMax)

/-- The shell `λθ. H_θ(H_θ(42))`, in Fω. -/
def tfbShellW : FTm := trTL (fun _ => natW) (fun _ => natW) TT.tfbShell

/-- **The ordinal rung as one Fω program.** -/
def tfbProgramW : FTm := .app tfbShellW thetaW

theorem check_tfbProgram : checkW 5 [] [] tfbProgramW = some natW := by decide +kernel

theorem cdepth_tfbProgram : cdepthF tfbProgramW ≤ 153 := by decide +kernel

/-- The rung as a ladder program at level `m`. -/
def rungProgram (m : Nat) : CTm (Atom m) := embC tfbProgramW

theorem infer_rungProgram {m : Nat} (hm : 5 ≤ m) : infer m [] [] (rungProgram m) = some FL.Ty.nat :=
  infer_embC check_tfbProgram hm [] []

/-- The rung program reduces to the numeral of the ordinal rung, under any oracle. -/
theorem steps_rungProgram (g : Nat → Nat) (m : Nat) :
    F.Steps g (erase (rungProgram m)) (F.Tm.num (F3 (F3 42))) := by
  show F.Steps g (FL.erase (embC tfbProgramW : CTm (Atom m))) _
  rw [erase_embC]
  show F.Steps g (F.Tm.app (eraseF tfbShellW) (eraseF thetaW)) _
  rw [show eraseF tfbShellW = TT.utrT TT.tfbShell from TFB.eraseF_trTL _ _ _]
  have h := TT.rel_utrT0 (f := g) TT.tfbShell (eraseF thetaW) Buch.thetaTFB rel_thetaW
  rw [TT.eval_tfbShell] at h
  exact h

/-- Every ladder maximum with budget `≥ 153` exceeds the ordinal rung, whatever the oracle. -/
theorem contender_3_lt_ladderMax (g : Nat → Nat) {m : Nat} (hm : 153 ≤ m) :
    contender_3 < ladderMax g m := by
  have hmem : rungProgram m ∈ ladderUpTo m :=
    FW.mem_ctmsUpTo (Atom.all m) tfbProgramW (Nat.le_trans cdepth_tfbProgram hm)
  have hv := fvalue_eq (ℓ := m) (infer_rungProgram (by omega)) (steps_rungProgram g m)
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
