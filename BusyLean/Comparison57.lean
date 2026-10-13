import BusyLean.Contender57
import BusyLean.Comparison56

/-! # Contender 57: comparison theorems -/

namespace BusyLean

theorem input_lt_family56 (n : Nat) : n < family56 n :=
  Nat.lt_trans (input_lt_F56 n) (input_lt_F56 (F56 n))

/-- At every input, `F57` exceeds Contender 56's family. -/
theorem family56_lt_F57 (n : Nat) : family56 n < F57 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (Ordinal.input_lt_numLift prims57
    (primEnv57 (family56 n) family56) family56 x)) (heightTree (family56 n)) (family56 n)).1
  have h2 := Ordinal.oracle_lt_numLift prims57 (primEnv57 (family56 n) family56) family56 (family56 n)
  exact Nat.lt_trans (input_lt_family56 (family56 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F57 (n : Nat) : n < F57 n :=
  Nat.lt_trans (input_lt_family56 n) (family56_lt_F57 n)

/-- **The required comparison**: Contender 56 is strictly smaller than Contender 57. -/
theorem contender_56_lt_contender_57 : contender_56 < contender_57 :=
  Nat.lt_trans (family56_lt_F57 42) (input_lt_F57 (F57 42))

theorem contender_55_lt_contender_57 : contender_55 < contender_57 :=
  Nat.lt_trans contender_55_lt_contender_56 contender_56_lt_contender_57

end BusyLean
