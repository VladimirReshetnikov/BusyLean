import BusyLean.Contender42
import BusyLean.Comparison41

/-! # Contender 42: comparison theorems -/

namespace BusyLean

theorem input_lt_family41 (n : Nat) : n < family41 n :=
  Nat.lt_trans (input_lt_F41 n) (input_lt_F41 (F41 n))

/-- At every input, `F42` exceeds Contender 41's family. -/
theorem family41_lt_F42 (n : Nat) : family41 n < F42 n :=
  Nat.lt_of_lt_of_le (input_lt_family41 (family41 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family41 x))
      (collapseTree (family41 n)) (family41 n)).1

theorem input_lt_F42 (n : Nat) : n < F42 n :=
  Nat.lt_trans (input_lt_family41 n) (family41_lt_F42 n)

/-- **The required comparison**: Contender 41 is strictly smaller than Contender 42. -/
theorem contender_41_lt_contender_42 : contender_41 < contender_42 :=
  Nat.lt_trans (family41_lt_F42 42) (input_lt_F42 (F42 42))

theorem contender_40_lt_contender_42 : contender_40 < contender_42 :=
  Nat.lt_trans contender_40_lt_contender_41 contender_41_lt_contender_42

end BusyLean
