import BusyLean.Contender51
import BusyLean.Comparison50

/-! # Contender 51: comparison theorems -/

namespace BusyLean

theorem input_lt_family50 (n : Nat) : n < family50 n :=
  Nat.lt_trans (input_lt_F50 n) (input_lt_F50 (F50 n))

/-- At every input, `F51` exceeds Contender 50's family. -/
theorem family50_lt_F51 (n : Nat) : family50 n < F51 n := by
  let N := family50 n
  let T := universeTree51 N
  have hHier :=
    (Ordinal.le_hier
      (fun x => Nat.le_of_lt (input_lt_ladderReflect family50 T x)) T N).1
  have hRead : family50 N < ladderReflect family50 T N :=
    Nat.lt_trans (oracle_lt_treeReflect family50 T N)
      (treeReflect_lt_ladderReflect family50 T N)
  exact Nat.lt_trans (input_lt_family50 N) (Nat.lt_of_lt_of_le hRead hHier)

theorem input_lt_F51 (n : Nat) : n < F51 n :=
  Nat.lt_trans (input_lt_family50 n) (family50_lt_F51 n)

/-- **The required comparison**: Contender 50 is strictly smaller. -/
theorem contender_50_lt_contender_51 : contender_50 < contender_51 :=
  Nat.lt_trans (family50_lt_F51 42) (input_lt_F51 (F51 42))

theorem contender_49_lt_contender_51 : contender_49 < contender_51 :=
  Nat.lt_trans contender_49_lt_contender_50 contender_50_lt_contender_51

end BusyLean
