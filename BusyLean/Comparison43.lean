import BusyLean.Contender43
import BusyLean.Comparison42

/-! # Contender 43: comparison theorems -/

namespace BusyLean

theorem input_lt_family42 (n : Nat) : n < family42 n :=
  Nat.lt_trans (input_lt_F42 n) (input_lt_F42 (F42 n))

/-- At every input, `F43` exceeds Contender 42's family. -/
theorem family42_lt_F43 (n : Nat) : family42 n < F43 n :=
  Nat.lt_of_lt_of_le (input_lt_family42 (family42 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family42 x))
      (collapseTree43 (family42 n)) (family42 n)).1

theorem input_lt_F43 (n : Nat) : n < F43 n :=
  Nat.lt_trans (input_lt_family42 n) (family42_lt_F43 n)

/-- **The required comparison**: Contender 42 is strictly smaller than Contender 43. -/
theorem contender_42_lt_contender_43 : contender_42 < contender_43 :=
  Nat.lt_trans (family42_lt_F43 42) (input_lt_F43 (F43 42))

theorem contender_41_lt_contender_43 : contender_41 < contender_43 :=
  Nat.lt_trans contender_41_lt_contender_42 contender_42_lt_contender_43

end BusyLean
