import BusyLean.Contender47
import BusyLean.Comparison46

/-! # Contender 47: comparison theorems -/

namespace BusyLean

theorem input_lt_family46 (n : Nat) : n < family46 n :=
  Nat.lt_trans (input_lt_F46 n) (input_lt_F46 (F46 n))

/-- At every input, `F47` exceeds Contender 46's family. -/
theorem family46_lt_F47 (n : Nat) : family46 n < F47 n :=
  Nat.lt_of_lt_of_le (input_lt_family46 (family46 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family46 x))
      (psiTree (family46 n)) (family46 n)).1

theorem input_lt_F47 (n : Nat) : n < F47 n :=
  Nat.lt_trans (input_lt_family46 n) (family46_lt_F47 n)

/-- **The required comparison**: Contender 46 is strictly smaller than Contender 47. -/
theorem contender_46_lt_contender_47 : contender_46 < contender_47 :=
  Nat.lt_trans (family46_lt_F47 42) (input_lt_F47 (F47 42))

theorem contender_45_lt_contender_47 : contender_45 < contender_47 :=
  Nat.lt_trans contender_45_lt_contender_46 contender_46_lt_contender_47

end BusyLean
