import BusyLean.Contender66
open BusyLean BusyLean.Ordinal BusyLean.Ordinal.PTL2

-- `metaStep S c = closeWith (towerFrom S c)` as a program of type `(C → C) → C → C`:
-- λS. λc. closeWith (towerFrom S c), with closeWith = prim 0 and towerFrom = prim 1.
def metaStepProg : Raw :=
  .lam stepTy (.lam closTy (.app (.prim 0) (.app (.app (.prim 1) (.var 1)) (.var 0))))
#eval ((infer prims66 [] metaStepProg).map (·.1)) == some (.arr stepTy stepTy)   -- true
#eval prims66.length                                                             -- 8
