import BusyLean.Comparison14
import Lean

#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.family13_lt_F14
#print axioms BusyLean.fvalue_lt_F14
#print axioms BusyLean.diagonalLift_rank_lt_succ

#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.fdDiagonal_rank_lt_succ
#check @BusyLean.fvalue_lt_F14

-- Small executable witnesses for the generic machinery only.  They do not
-- unfold any contender.
def tinySeed : BusyLean.W.Family := fun i n => i + n

def tinyProgressive : BusyLean.Transformer := fun seed _ n => seed 0 n + n + 1

#eval (BusyLean.stageLift BusyLean.liftTransformer tinyProgressive .leaf tinySeed 0 0)
