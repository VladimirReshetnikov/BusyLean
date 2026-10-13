import BusyLean.Contender12
import BusyLean.MetaReflectionFacts
import BusyLean.Comparison11

/-! # Contender 12: comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- Kind-polymorphic Fω reflection is progressive. -/
theorem fkTransformer_progressive : Progressive fkTransformer := by
  intro seed i o n hi
  exact oracle_lt_reflect11 seed hi

/-- At every input, `F12` exceeds Contender 11's family. -/
theorem family11_lt_F12 (n : Nat) : family11 n < F12 n :=
  operatorStage_progressive fkTransformer fkTransformer_progressive tree12
    (fun _ => family11) 0 n n (Nat.zero_le n)

theorem input_lt_F10 (n : Nat) : n < F10 n := Fk.input_lt_reflectFk family9 n

theorem input_lt_family11 (n : Nat) : n < family11 n :=
  Nat.lt_trans (input_lt_stage11 _ index n) (input_lt_stage11 _ index (F11 n))

theorem input_lt_F12 (n : Nat) : n < F12 n :=
  Nat.lt_trans (input_lt_family11 n) (family11_lt_F12 n)

/-- **The required comparison**: Contender 11 is strictly smaller than Contender 12. -/
theorem contender_11_lt_contender_12 : contender_11 < contender_12 :=
  Nat.lt_trans (family11_lt_F12 42) (input_lt_F12 (F12 42))

theorem contender_10_lt_contender_12 : contender_10 < contender_12 :=
  Nat.lt_trans contender_10_lt_contender_11 contender_11_lt_contender_12

end BusyLean
