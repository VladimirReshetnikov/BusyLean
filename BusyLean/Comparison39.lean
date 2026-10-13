import BusyLean.Contender39
import BusyLean.Comparison38

/-! # Contender 39: comparison theorems -/

namespace BusyLean

theorem input_lt_family38 (n : Nat) : n < family38 n :=
  Nat.lt_trans (input_lt_F38 n) (input_lt_F38 (F38 n))

/-- At every input, `F39` exceeds Contender 38's family. -/
theorem family38_lt_F39 (n : Nat) : family38 n < F39 n :=
  Nat.lt_of_lt_of_le (input_lt_family38 (family38 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family38 x))
      (mixTree (family38 n)) (family38 n)).1

theorem input_lt_F39 (n : Nat) : n < F39 n :=
  Nat.lt_trans (input_lt_family38 n) (family38_lt_F39 n)

/-- **The required comparison**: Contender 38 is strictly smaller than Contender 39. -/
theorem contender_38_lt_contender_39 : contender_38 < contender_39 :=
  Nat.lt_trans (family38_lt_F39 42) (input_lt_F39 (F39 42))

theorem contender_37_lt_contender_39 : contender_37 < contender_39 :=
  Nat.lt_trans contender_37_lt_contender_38 contender_38_lt_contender_39

end BusyLean
