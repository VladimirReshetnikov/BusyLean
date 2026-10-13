import BusyLean.Contender44
import BusyLean.Comparison43

/-! # Contender 44: comparison theorems -/

namespace BusyLean

theorem input_lt_family43 (n : Nat) : n < family43 n :=
  Nat.lt_trans (input_lt_F43 n) (input_lt_F43 (F43 n))

/-- At every input, `F44` exceeds Contender 43's family. -/
theorem family43_lt_F44 (n : Nat) : family43 n < F44 n :=
  Nat.lt_of_lt_of_le (input_lt_family43 (family43 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family43 x))
      (levelTree44 (family43 n)) (family43 n)).1

theorem input_lt_F44 (n : Nat) : n < F44 n :=
  Nat.lt_trans (input_lt_family43 n) (family43_lt_F44 n)

/-- **The required comparison**: Contender 43 is strictly smaller than Contender 44. -/
theorem contender_43_lt_contender_44 : contender_43 < contender_44 :=
  Nat.lt_trans (family43_lt_F44 42) (input_lt_F44 (F44 42))

theorem contender_42_lt_contender_44 : contender_42 < contender_44 :=
  Nat.lt_trans contender_42_lt_contender_43 contender_43_lt_contender_44

end BusyLean
