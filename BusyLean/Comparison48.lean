import BusyLean.Contender48
import BusyLean.Comparison47

/-! # Contender 48: comparison theorems -/

namespace BusyLean

theorem input_lt_family47 (n : Nat) : n < family47 n :=
  Nat.lt_trans (input_lt_F47 n) (input_lt_F47 (F47 n))

/-- At every input, `F48` exceeds Contender 47's family. -/
theorem family47_lt_F48 (n : Nat) : family47 n < F48 n :=
  Nat.lt_of_lt_of_le (input_lt_family47 (family47 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family47 x))
      (levelIterTree (family47 n)) (family47 n)).1

theorem input_lt_F48 (n : Nat) : n < F48 n :=
  Nat.lt_trans (input_lt_family47 n) (family47_lt_F48 n)

/-- **The required comparison**: Contender 47 is strictly smaller than Contender 48. -/
theorem contender_47_lt_contender_48 : contender_47 < contender_48 :=
  Nat.lt_trans (family47_lt_F48 42) (input_lt_F48 (F48 42))

theorem contender_46_lt_contender_48 : contender_46 < contender_48 :=
  Nat.lt_trans contender_46_lt_contender_47 contender_47_lt_contender_48

end BusyLean
