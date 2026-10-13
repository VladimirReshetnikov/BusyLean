import BusyLean.Contender58
import BusyLean.Comparison57

/-! # Contender 58: comparison theorems -/

namespace BusyLean

theorem oracle_lt_towerClosure (N : Nat) (g : Nat → Nat) (m : Nat) :
    g m < towerClosure N g m :=
  Ordinal.oracle_lt_numLift _ _ g m

theorem input_lt_towerClosure (N : Nat) (g : Nat → Nat) (m : Nat) :
    m < towerClosure N g m :=
  Ordinal.input_lt_numLift _ _ g m

theorem input_lt_family57 (n : Nat) : n < family57 n :=
  Nat.lt_trans (input_lt_F57 n) (input_lt_F57 (F57 n))

/-- At every input, `F58` exceeds Contender 57's family. -/
theorem family57_lt_F58 (n : Nat) : family57 n < F58 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_towerClosure (family57 n) family57 x))
    (towerTree (family57 n)) (family57 n)).1
  have h2 := oracle_lt_towerClosure (family57 n) family57 (family57 n)
  exact Nat.lt_trans (input_lt_family57 (family57 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F58 (n : Nat) : n < F58 n :=
  Nat.lt_trans (input_lt_family57 n) (family57_lt_F58 n)

/-- **The required comparison**: Contender 57 is strictly smaller than Contender 58. -/
theorem contender_57_lt_contender_58 : contender_57 < contender_58 :=
  Nat.lt_trans (family57_lt_F58 42) (input_lt_F58 (F58 42))

theorem contender_56_lt_contender_58 : contender_56 < contender_58 :=
  Nat.lt_trans contender_56_lt_contender_57 contender_57_lt_contender_58

end BusyLean
