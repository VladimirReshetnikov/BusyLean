import BusyLean.Independent.TreeLang

/-!
# Depth bounds for `TT` programs (proof infrastructure)

`tdTT` and `cdTT` bound the depths of the Church-style ladder translations of
`TT` types and terms (`tdepth_tyTT`, `cdepth_trTC_le` in `EpsLtLadder.lean`).
They are computed on `TT` syntax alone, so the kernel checks the bound for
`omegaProgram` here, in parallel with the embedding proofs.
-/

namespace BusyLean.Indep

open BusyLean.Indep.TT

/-- The depth of `tyTT a`. -/
def tdTT : TT.Ty → Nat
  | .nat => 5
  | .tree => 11
  | .lev m => 8 * m + 13
  | .arr a b => max (tdTT a) (tdTT b) + 1

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
  | _, _, .lzero m => 8 * m + 25
  | _, _, .lsucc m => 8 * m + 35
  | _, _, .llim m => 8 * m + 45
  | _, _, .lsup m => 8 * m + 55
  | _, _, .lsup0 => 60
  | _, _, .lfold0 r => tdTT r + 35
  | _, _, .lfoldS m r => tdTT r + 8 * m + 45

theorem cdTT_omegaProgram : cdTT omegaProgram ≤ 500 := by decide +kernel

end BusyLean.Indep
