import BusyLean.Contender40
import BusyLean.Comparison39

/-! # Contender 40: comparison theorems -/

namespace BusyLean

theorem input_lt_family39 (n : Nat) : n < family39 n :=
  Nat.lt_trans (input_lt_F39 n) (input_lt_F39 (F39 n))

/-- At every input, `F40` exceeds Contender 39's family. -/
theorem family39_lt_F40 (n : Nat) : family39 n < F40 n :=
  Nat.lt_of_lt_of_le (input_lt_family39 (family39 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family39 x))
      (metaTree (family39 n)) (family39 n)).1

theorem input_lt_F40 (n : Nat) : n < F40 n :=
  Nat.lt_trans (input_lt_family39 n) (family39_lt_F40 n)

/-- **The required comparison**: Contender 39 is strictly smaller than Contender 40. -/
theorem contender_39_lt_contender_40 : contender_39 < contender_40 :=
  Nat.lt_trans (family39_lt_F40 42) (input_lt_F40 (F40 42))

theorem contender_38_lt_contender_40 : contender_38 < contender_40 :=
  Nat.lt_trans contender_38_lt_contender_39 contender_39_lt_contender_40

end BusyLean
