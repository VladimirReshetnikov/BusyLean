import Hierarchy
import OracleFacts

namespace Biggest

theorem contender_5_lt_contender_6 : contender_5 < contender_6 := by
  unfold contender_6 finalStage
  exact baseline_lt_reflect _ 42

end Biggest

#print axioms Biggest.contender_5
#print axioms Biggest.contender_6
#print axioms Biggest.contender_5_lt_contender_6
