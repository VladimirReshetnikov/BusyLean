import BusyLean.Contender67
import BusyLean.Comparison66

/-! # Contender 67: comparison theorems -/

namespace BusyLean

open Ordinal (CTree Closures)

/-- Every level of the reflective tower is good for every family. -/
theorem good_cwTower (N : Nat) (g0 : Nat → Nat) :
    ∀ (a : CTree) (H : CTree → Closures), Good (cwTower N g0 a H) := by
  intro a
  induction a with
  | zero => intro H; exact good_num2Lift _ _ _
  | succ a _ => intro H; exact good_num2Lift _ _ _
  | lim f ih => intro H; exact good_lim _ _ fun i => ih i H
  | supL _ _ => intro H; exact good_num2Lift _ _ _
  | supH _ _ => intro H; exact good_num2Lift _ _ _

theorem input_lt_family66 (n : Nat) : n < family66 n :=
  Nat.lt_trans (input_lt_F66 n) (input_lt_F66 (F66 n))

/-- At every input, `F67` exceeds Contender 66's family. -/
theorem family66_lt_F67 (n : Nat) : family66 n < F67 n := by
  have hS := good_cwTower (family66 n) family66 (cwTree (family66 n)) (const61 (family66 n) family66)
    family66
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (cwTree (family66 n)) (family66 n)).1
  exact Nat.lt_trans (input_lt_family66 (family66 n)) (Nat.lt_of_lt_of_le (hS (family66 n)).1 h1)

theorem input_lt_F67 (n : Nat) : n < F67 n :=
  Nat.lt_trans (input_lt_family66 n) (family66_lt_F67 n)

/-- **The required comparison**: Contender 66 is strictly smaller than Contender 67. -/
theorem contender_66_lt_contender_67 : contender_66 < contender_67 :=
  Nat.lt_trans (family66_lt_F67 42) (input_lt_F67 (F67 42))

theorem contender_65_lt_contender_67 : contender_65 < contender_67 :=
  Nat.lt_trans contender_65_lt_contender_66 contender_66_lt_contender_67

end BusyLean
