import BusyLean.Contender51
import BusyLean.Comparison50

/-! # Contender 51: comparison theorems -/

namespace BusyLean

theorem input_lt_family50 (n : Nat) : n < family50 n :=
  Nat.lt_trans (input_lt_F50 n) (input_lt_F50 (F50 n))

/-- At every input, `F51` exceeds Contender 50's family. -/
theorem family50_lt_F51 (n : Nat) : family50 n < F51 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_ladderReflect family50
    (primTree (family50 n)) x)) (primTree (family50 n)) (family50 n)).1
  have h2 := Nat.lt_trans (oracle_lt_treeReflect family50 (primTree (family50 n)) (family50 n))
    (treeReflect_lt_ladderReflect family50 (primTree (family50 n)) (family50 n))
  exact Nat.lt_trans (input_lt_family50 (family50 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F51 (n : Nat) : n < F51 n :=
  Nat.lt_trans (input_lt_family50 n) (family50_lt_F51 n)

/-- **The required comparison**: Contender 50 is strictly smaller than Contender 51. -/
theorem contender_50_lt_contender_51 : contender_50 < contender_51 :=
  Nat.lt_trans (family50_lt_F51 42) (input_lt_F51 (F51 42))

theorem contender_49_lt_contender_51 : contender_49 < contender_51 :=
  Nat.lt_trans contender_49_lt_contender_50 contender_50_lt_contender_51

end BusyLean
