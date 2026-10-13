import BusyLean.Contender45
import BusyLean.Comparison44

/-! # Contender 45: comparison theorems -/

namespace BusyLean

theorem input_lt_family44 (n : Nat) : n < family44 n :=
  Nat.lt_trans (input_lt_F44 n) (input_lt_F44 (F44 n))

/-- At every input, `F45` exceeds Contender 44's family. -/
theorem family44_lt_F45 (n : Nat) : family44 n < F45 n :=
  Nat.lt_of_lt_of_le (input_lt_family44 (family44 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family44 x))
      (thetaTree (family44 n)) (family44 n)).1

theorem input_lt_F45 (n : Nat) : n < F45 n :=
  Nat.lt_trans (input_lt_family44 n) (family44_lt_F45 n)

/-- **The required comparison**: Contender 44 is strictly smaller than Contender 45. -/
theorem contender_44_lt_contender_45 : contender_44 < contender_45 :=
  Nat.lt_trans (family44_lt_F45 42) (input_lt_F45 (F45 42))

theorem contender_43_lt_contender_45 : contender_43 < contender_45 :=
  Nat.lt_trans contender_43_lt_contender_44 contender_44_lt_contender_45

end BusyLean
