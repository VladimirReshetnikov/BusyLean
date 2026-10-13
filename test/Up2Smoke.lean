import BusyLean.Contender63
open BusyLean BusyLean.Ordinal BusyLean.Ordinal.PTL2

-- `up2` maps families to families; applied twice to the stack family, then to the seed:
#eval ((infer prims63 [] (.app (.app (.prim 1) (.app (.prim 1) (.prim 0))) (.prim 2))).map (·.1))
  == some closTy                                                        -- true
-- Contender 61's primitives sit below the two new ones.
#eval prims63.length                                                     -- 8
