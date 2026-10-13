import BusyLean.Contender49
import BusyLean.Comparison48

/-! # Contender 49: comparison theorems -/

namespace BusyLean

theorem input_lt_family48 (n : Nat) : n < family48 n :=
  Nat.lt_trans (input_lt_F48 n) (input_lt_F48 (F48 n))

/-- At every input, `F49` exceeds Contender 48's family. -/
theorem family48_lt_F49 (n : Nat) : family48 n < F49 n :=
  Nat.lt_of_lt_of_le (input_lt_family48 (family48 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family48 x))
      (universeTree49 (family48 n)) (family48 n)).1

theorem input_lt_F49 (n : Nat) : n < F49 n :=
  Nat.lt_trans (input_lt_family48 n) (family48_lt_F49 n)

/-- **The required comparison**: Contender 48 is strictly smaller. -/
theorem contender_48_lt_contender_49 : contender_48 < contender_49 :=
  Nat.lt_trans (family48_lt_F49 42) (input_lt_F49 (F49 42))

theorem contender_47_lt_contender_49 : contender_47 < contender_49 :=
  Nat.lt_trans contender_47_lt_contender_48 contender_48_lt_contender_49

end BusyLean
