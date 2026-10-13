import BusyLean.Contender68
open BusyLean BusyLean.Ordinal BusyLean.Ordinal.PTL2

-- cwStep applied twice to the tower at the seed's height has the operator type.
#eval ((infer prims68 [] (.app (.prim 0) (.app (.prim 0) (.app (.prim 1) (.prim 4))))).map (·.1))
  == some cwTy                                                               -- true
#eval prims68.length                                                         -- 10
