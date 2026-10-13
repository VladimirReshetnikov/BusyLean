import BusyLean.Contender5
open BusyLean.C5
-- Upstream `Goal lookup [10; 11; 12] 0 = Some 12.` etc.
example : lookup [10, 11, 12] 0 = some 12 := rfl
example : lookup [10, 11, 12] 2 = some 10 := rfl
example : lookup [10, 11, 12] 3 = none := rfl
#eval (List.range 5).map fun n => (typesUpTo n).length
#eval (List.range 5).map fun n => (termsUpTo n).length
#eval (List.range 5).map largestSTLCNatRecNatOfDepth
-- `S S` evaluates to 1 under the error-cast convention (noted by P2).
#eval eval (.app .succ .succ)
