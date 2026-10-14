import BusyLean.Independent.AckermannLtSystemT
import BusyLean.Independent.SystemTLtEps
import BusyLean.Independent.EpsLtLadder

/-!
# The independent tower in one statement

`contender_1 < contender_2 < contender_3 < contender_4`, checked in a single
module that imports all three comparisons.
-/

namespace BusyLean.Indep

theorem independent_tower :
    contender_1 < contender_2 ∧ contender_2 < contender_3 ∧ contender_3 < contender_4 :=
  ⟨contender_1_lt_contender_2, contender_2_lt_contender_3, contender_3_lt_contender_4⟩

theorem contender_1_lt_contender_4 : contender_1 < contender_4 :=
  Nat.lt_trans contender_1_lt_contender_2 (Nat.lt_trans contender_2_lt_contender_3
    contender_3_lt_contender_4)

end BusyLean.Indep
