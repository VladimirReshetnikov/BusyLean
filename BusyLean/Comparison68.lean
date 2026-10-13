import BusyLean.Contender68
import BusyLean.Comparison67

/-! # Contender 68: comparison theorems -/

namespace BusyLean

theorem oracle_lt_cwStepClosure (N : Nat) (g : Nat → Nat) (m : Nat) : g m < cwStepClosure N g m :=
  Ordinal.oracle_lt_num2Lift _ _ g m

theorem input_lt_cwStepClosure (N : Nat) (g : Nat → Nat) (m : Nat) : m < cwStepClosure N g m :=
  Ordinal.input_lt_num2Lift _ _ g m

theorem input_lt_family67 (n : Nat) : n < family67 n :=
  Nat.lt_trans (input_lt_F67 n) (input_lt_F67 (F67 n))

/-- At every input, `F68` exceeds Contender 67's family. -/
theorem family67_lt_F68 (n : Nat) : family67 n < F68 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_cwStepClosure (family67 n) family67 x))
    (cwStepTree (family67 n)) (family67 n)).1
  have h2 := oracle_lt_cwStepClosure (family67 n) family67 (family67 n)
  exact Nat.lt_trans (input_lt_family67 (family67 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F68 (n : Nat) : n < F68 n :=
  Nat.lt_trans (input_lt_family67 n) (family67_lt_F68 n)

/-- **The required comparison**: Contender 67 is strictly smaller than Contender 68. -/
theorem contender_67_lt_contender_68 : contender_67 < contender_68 :=
  Nat.lt_trans (family67_lt_F68 42) (input_lt_F68 (F68 42))

theorem contender_66_lt_contender_68 : contender_66 < contender_68 :=
  Nat.lt_trans contender_66_lt_contender_67 contender_67_lt_contender_68

end BusyLean
