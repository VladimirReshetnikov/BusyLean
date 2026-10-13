import BusyLean.Contender70
import BusyLean.Comparison69

/-! # Contender 70: comparison theorems -/

namespace BusyLean

theorem good_cycleTower (N : Nat) (g : Nat → Nat) (T : Ordinal.CTree) : Good (cycleTower N g T) :=
  good_cwTowerP _ _ T _

theorem input_lt_family69 (n : Nat) : n < family69 n :=
  Nat.lt_trans (input_lt_F69 n) (input_lt_F69 (F69 n))

/-- At every input, `F70` exceeds Contender 69's family. -/
theorem family69_lt_F70 (n : Nat) : family69 n < F70 n := by
  have hS := good_cycleTower (family69 n) family69 (cycleTree (family69 n)) family69
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (cycleTree (family69 n)) (family69 n)).1
  exact Nat.lt_trans (input_lt_family69 (family69 n)) (Nat.lt_of_lt_of_le (hS (family69 n)).1 h1)

theorem input_lt_F70 (n : Nat) : n < F70 n :=
  Nat.lt_trans (input_lt_family69 n) (family69_lt_F70 n)

/-- **The required comparison**: Contender 69 is strictly smaller than Contender 70. -/
theorem contender_69_lt_contender_70 : contender_69 < contender_70 :=
  Nat.lt_trans (family69_lt_F70 42) (input_lt_F70 (F70 42))

theorem contender_68_lt_contender_70 : contender_68 < contender_70 :=
  Nat.lt_trans contender_68_lt_contender_69 contender_69_lt_contender_70

end BusyLean
