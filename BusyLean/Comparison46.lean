import BusyLean.Contender46
import BusyLean.Comparison45

/-! # Contender 46: comparison theorems -/

namespace BusyLean

theorem input_lt_family45 (n : Nat) : n < family45 n :=
  Nat.lt_trans (input_lt_F45 n) (input_lt_F45 (F45 n))

/-- At every input, `F46` exceeds Contender 45's family. -/
theorem family45_lt_F46 (n : Nat) : family45 n < F46 n :=
  Nat.lt_of_lt_of_le (input_lt_family45 (family45 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family45 x))
      (univTree46 (family45 n)) (family45 n)).1

theorem input_lt_F46 (n : Nat) : n < F46 n :=
  Nat.lt_trans (input_lt_family45 n) (family45_lt_F46 n)

/-- **The required comparison**: Contender 45 is strictly smaller than Contender 46. -/
theorem contender_45_lt_contender_46 : contender_45 < contender_46 :=
  Nat.lt_trans (family45_lt_F46 42) (input_lt_F46 (F46 42))

theorem contender_44_lt_contender_46 : contender_44 < contender_46 :=
  Nat.lt_trans contender_44_lt_contender_45 contender_45_lt_contender_46

end BusyLean
