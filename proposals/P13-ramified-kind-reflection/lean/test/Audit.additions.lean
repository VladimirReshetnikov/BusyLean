-- Add after the Contender 10 audit declarations.
#print axioms BusyLean.contender_11
#print axioms BusyLean.contender_10_lt_contender_11
#print axioms BusyLean.family10_lt_F11
#print axioms BusyLean.fixed_rank_eventually_lt_F11
#print axioms BusyLean.fvalue_lt_F11
#print axioms BusyLean.RK.ramified_dominates
#print axioms BusyLean.RK.ramified_lt_of_lt

#assert_not_in_closure BusyLean.contender_11 :
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_10_lt_contender_11
#check @BusyLean.fixed_rank_eventually_lt_F11
#check @BusyLean.fvalue_lt_F11
#check @BusyLean.RK.ramified_level_lt
