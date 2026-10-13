import BusyLean.Contender41
import BusyLean.Comparison40

/-! # Contender 41: comparison theorems -/

namespace BusyLean

theorem input_lt_family40 (n : Nat) : n < family40 n :=
  Nat.lt_trans (input_lt_F40 n) (input_lt_F40 (F40 n))

/-- At every input, `F41` exceeds Contender 40's family. -/
theorem family40_lt_F41 (n : Nat) : family40 n < F41 n :=
  Nat.lt_of_lt_of_le (input_lt_family40 (family40 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family40 x))
      (readerTree (family40 n)) (family40 n)).1

theorem input_lt_F41 (n : Nat) : n < F41 n :=
  Nat.lt_trans (input_lt_family40 n) (family40_lt_F41 n)

/-- **The required comparison**: Contender 40 is strictly smaller than Contender 41. -/
theorem contender_40_lt_contender_41 : contender_40 < contender_41 :=
  Nat.lt_trans (family40_lt_F41 42) (input_lt_F41 (F41 42))

theorem contender_39_lt_contender_41 : contender_39 < contender_41 :=
  Nat.lt_trans contender_39_lt_contender_40 contender_40_lt_contender_41

end BusyLean
