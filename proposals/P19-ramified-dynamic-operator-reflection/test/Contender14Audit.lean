import BusyLean.Comparison14
import Lean

/-!
Standalone audit additions for Contender 14.  The repository's existing
`test/Audit.lean` defines `#assert_not_in_closure`; the integration patch adds
the same checks there.  This file concentrates the ordinary kernel reports.
-/

#print axioms BusyLean.reflectFdFamily
#print axioms BusyLean.fdFamilyTransformer
#print axioms BusyLean.operatorTower
#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.fortyTwo_F13_steps_lt_F14
#print axioms BusyLean.fvalue_lt_contender_14

#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.fortyTwo_F13_steps_lt_F14
#check @BusyLean.seed13_lt_F14
#check @BusyLean.fvalue_lt_contender_14
