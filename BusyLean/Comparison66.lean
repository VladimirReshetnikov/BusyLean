import BusyLean.Contender66
import BusyLean.Comparison65

/-! # Contender 66: comparison theorems -/

namespace BusyLean

theorem oracle_lt_closeClosure (N : Nat) (g : Nat → Nat) (m : Nat) : g m < closeClosure N g m :=
  Ordinal.oracle_lt_num2Lift _ _ g m

theorem input_lt_closeClosure (N : Nat) (g : Nat → Nat) (m : Nat) : m < closeClosure N g m :=
  Ordinal.input_lt_num2Lift _ _ g m

theorem input_lt_family65 (n : Nat) : n < family65 n :=
  Nat.lt_trans (input_lt_F65 n) (input_lt_F65 (F65 n))

/-- At every input, `F66` exceeds Contender 65's family. -/
theorem family65_lt_F66 (n : Nat) : family65 n < F66 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_closeClosure (family65 n) family65 x))
    (closeTree (family65 n)) (family65 n)).1
  have h2 := oracle_lt_closeClosure (family65 n) family65 (family65 n)
  exact Nat.lt_trans (input_lt_family65 (family65 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F66 (n : Nat) : n < F66 n :=
  Nat.lt_trans (input_lt_family65 n) (family65_lt_F66 n)

/-- **The required comparison**: Contender 65 is strictly smaller than Contender 66. -/
theorem contender_65_lt_contender_66 : contender_65 < contender_66 :=
  Nat.lt_trans (family65_lt_F66 42) (input_lt_F66 (F66 42))

theorem contender_64_lt_contender_66 : contender_64 < contender_66 :=
  Nat.lt_trans contender_64_lt_contender_65 contender_65_lt_contender_66

end BusyLean
