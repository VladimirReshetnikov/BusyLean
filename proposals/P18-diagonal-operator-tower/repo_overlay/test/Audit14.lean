/-!
Append the following declarations to `test/Audit.lean` after importing
`BusyLean.Contender14` and `BusyLean.Comparison14` through `BusyLean.lean`.
-/

#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.family13_lt_F14
#print axioms BusyLean.fvalue_lt_reflect14
#print axioms BusyLean.fvalue_lt_F14
#print axioms BusyLean.diagonalOperatorTower_step_lt
#print axioms BusyLean.diagonalOperatorTower_rank_lt

#assert_not_in_closure BusyLean.contender_14 :
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.family13_lt_F14
#check @BusyLean.diagonalOperatorTower_step_lt
#check @BusyLean.diagonalOperatorTower_rank_lt
#check @BusyLean.fvalue_lt_F14
