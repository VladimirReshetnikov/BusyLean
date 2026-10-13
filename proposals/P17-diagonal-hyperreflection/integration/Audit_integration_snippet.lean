-- Optional lines to merge into test/Audit.lean after importing Comparison14.
#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.family13_lt_F14
#print axioms BusyLean.fvalue_lt_F14
#print axioms BusyLean.diagonalLift_rank_lt_succ

#assert_not_in_closure BusyLean.contender_14 :
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.fdDiagonal_rank_lt_succ
#check @BusyLean.fvalue_lt_F14
