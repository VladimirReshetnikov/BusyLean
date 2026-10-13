import BusyLean.Contender69
import BusyLean.Comparison68

/-! # Contender 69: comparison theorems -/

namespace BusyLean

open Ordinal (CTree Closures)

/-- Every level of the generic reflective tower is good for every family. -/
theorem good_cwTowerP (P : List Ordinal.PTL2.Ty) (σ : Ordinal.PTL2.Env P) :
    ∀ (a : CTree) (H : CTree → Closures), Good (cwTowerP P σ a H) := by
  intro a
  induction a with
  | zero => intro H; exact good_num2Lift _ _ _
  | succ a _ => intro H; exact good_num2Lift _ _ _
  | lim f ih => intro H; exact good_lim _ _ fun i => ih i H
  | supL _ _ => intro H; exact good_num2Lift _ _ _
  | supH _ _ => intro H; exact good_num2Lift _ _ _

theorem input_lt_family68 (n : Nat) : n < family68 n :=
  Nat.lt_trans (input_lt_F68 n) (input_lt_F68 (F68 n))

/-- At every input, `F69` exceeds Contender 68's family. -/
theorem family68_lt_F69 (n : Nat) : family68 n < F69 n := by
  have hS := good_cwTowerP prims68 (primEnv68 (family68 n) family68) (cwTreeP (family68 n))
    (const61 (family68 n) family68) family68
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (cwTreeP (family68 n)) (family68 n)).1
  exact Nat.lt_trans (input_lt_family68 (family68 n)) (Nat.lt_of_lt_of_le (hS (family68 n)).1 h1)

theorem input_lt_F69 (n : Nat) : n < F69 n :=
  Nat.lt_trans (input_lt_family68 n) (family68_lt_F69 n)

/-- **The required comparison**: Contender 68 is strictly smaller than Contender 69. -/
theorem contender_68_lt_contender_69 : contender_68 < contender_69 :=
  Nat.lt_trans (family68_lt_F69 42) (input_lt_F69 (F69 42))

theorem contender_67_lt_contender_69 : contender_67 < contender_69 :=
  Nat.lt_trans contender_67_lt_contender_68 contender_68_lt_contender_69

end BusyLean
