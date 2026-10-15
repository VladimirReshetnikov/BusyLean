import BusyLean.Independent.AckermannLtSystemT
import BusyLean.Independent.SystemTLtEps
import BusyLean.Independent.EpsLtLadder
import BusyLean.Independent.LadderOldLtLadder

/-!
# The independent tower in one statement

`contender_1 < contender_2 < contender_3 < contender_4`, checked in a single
module that imports all three comparisons. Rung 4 also exceeds its previous
version, which it incorporates (`contender_4_old_lt_contender_4`).
-/

namespace BusyLean.Indep

theorem independent_tower :
    contender_1 < contender_2 ∧ contender_2 < contender_3 ∧ contender_3 < contender_4 :=
  ⟨contender_1_lt_contender_2, contender_2_lt_contender_3, contender_3_lt_contender_4⟩

theorem contender_1_lt_contender_4 : contender_1 < contender_4 :=
  Nat.lt_trans contender_1_lt_contender_2 (Nat.lt_trans contender_2_lt_contender_3
    contender_3_lt_contender_4)

end BusyLean.Indep
