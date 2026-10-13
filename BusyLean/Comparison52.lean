import BusyLean.Contender52
import BusyLean.Comparison51

/-! # Contender 52: comparison theorems -/

namespace BusyLean

theorem input_lt_family51 (n : Nat) : n < family51 n :=
  Nat.lt_trans (input_lt_F51 n) (input_lt_F51 (F51 n))

/-- At every input, `F52` exceeds Contender 51's family. -/
theorem family51_lt_F52 (n : Nat) : family51 n < F52 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_ladderReflect family51
    (stackTree (family51 n)) x)) (stackTree (family51 n)) (family51 n)).1
  have h2 := Nat.lt_trans (oracle_lt_treeReflect family51 (stackTree (family51 n)) (family51 n))
    (treeReflect_lt_ladderReflect family51 (stackTree (family51 n)) (family51 n))
  exact Nat.lt_trans (input_lt_family51 (family51 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F52 (n : Nat) : n < F52 n :=
  Nat.lt_trans (input_lt_family51 n) (family51_lt_F52 n)

/-- **The required comparison**: Contender 51 is strictly smaller than Contender 52. -/
theorem contender_51_lt_contender_52 : contender_51 < contender_52 :=
  Nat.lt_trans (family51_lt_F52 42) (input_lt_F52 (F52 42))

theorem contender_50_lt_contender_52 : contender_50 < contender_52 :=
  Nat.lt_trans contender_50_lt_contender_51 contender_51_lt_contender_52

end BusyLean
