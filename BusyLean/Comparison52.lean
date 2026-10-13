import BusyLean.Contender52
import BusyLean.Comparison51

/-! # Contender 52: comparison theorems -/

namespace BusyLean

theorem input_lt_family51 (n : Nat) : n < family51 n :=
  Nat.lt_trans (input_lt_F51 n) (input_lt_F51 (F51 n))

/-- At every input, `F52` exceeds Contender 51's family. -/
theorem family51_lt_F52 (n : Nat) : family51 n < F52 n := by
  let N := family51 n
  let T := universeTree52 N
  have hHier :=
    (Ordinal.le_hier
      (fun x => Nat.le_of_lt (input_lt_ladderReflect family51 T x)) T N).1
  have hRead : family51 N < ladderReflect family51 T N :=
    Nat.lt_trans (oracle_lt_treeReflect family51 T N)
      (treeReflect_lt_ladderReflect family51 T N)
  exact Nat.lt_trans (input_lt_family51 N) (Nat.lt_of_lt_of_le hRead hHier)

theorem input_lt_F52 (n : Nat) : n < F52 n :=
  Nat.lt_trans (input_lt_family51 n) (family51_lt_F52 n)

/-- **The required comparison**: Contender 51 is strictly smaller. -/
theorem contender_51_lt_contender_52 : contender_51 < contender_52 :=
  Nat.lt_trans (family51_lt_F52 42) (input_lt_F52 (F52 42))

theorem contender_50_lt_contender_52 : contender_50 < contender_52 :=
  Nat.lt_trans contender_50_lt_contender_51 contender_51_lt_contender_52

end BusyLean
