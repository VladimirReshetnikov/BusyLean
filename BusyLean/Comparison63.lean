import BusyLean.Contender63
import BusyLean.Comparison62

/-! # Contender 63: comparison theorems -/

namespace BusyLean

theorem oracle_lt_up2Closure (N : Nat) (g : Nat → Nat) (m : Nat) : g m < up2Closure N g m :=
  Ordinal.oracle_lt_num2Lift _ _ g m

theorem input_lt_up2Closure (N : Nat) (g : Nat → Nat) (m : Nat) : m < up2Closure N g m :=
  Ordinal.input_lt_num2Lift _ _ g m

theorem input_lt_family62 (n : Nat) : n < family62 n :=
  Nat.lt_trans (input_lt_F62 n) (input_lt_F62 (F62 n))

/-- At every input, `F63` exceeds Contender 62's family. -/
theorem family62_lt_F63 (n : Nat) : family62 n < F63 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_up2Closure (family62 n) family62 x))
    (up2Tree (family62 n)) (family62 n)).1
  have h2 := oracle_lt_up2Closure (family62 n) family62 (family62 n)
  exact Nat.lt_trans (input_lt_family62 (family62 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F63 (n : Nat) : n < F63 n :=
  Nat.lt_trans (input_lt_family62 n) (family62_lt_F63 n)

/-- **The required comparison**: Contender 62 is strictly smaller than Contender 63. -/
theorem contender_62_lt_contender_63 : contender_62 < contender_63 :=
  Nat.lt_trans (family62_lt_F63 42) (input_lt_F63 (F63 42))

theorem contender_61_lt_contender_63 : contender_61 < contender_63 :=
  Nat.lt_trans contender_61_lt_contender_62 contender_62_lt_contender_63

end BusyLean
