import BusyLean.Contender67
open BusyLean BusyLean.Ordinal BusyLean.Ordinal.PTL2

-- At level a+1 the previous operator is a primitive (index 1) of type (tree → C) → C;
-- applying it to the family (index 0) gives a closure pair.
#eval ((infer (famTy :: cwTy :: prims66) [] (.app (.prim 1) (.prim 0))).map (·.1)) == some closTy  -- true
#eval (famTy :: cwTy :: prims66).length                                                         -- 10
