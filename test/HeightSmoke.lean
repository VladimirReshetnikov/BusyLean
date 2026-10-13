import BusyLean.Contender57
open BusyLean BusyLean.Ordinal

-- The closed `nat` programs of size ≤ 1 over prims57 are just `zero`
-- (the number oracle needs an application, which needs size 2).
#eval (PTL.natsUpTo prims57 (primEnv57 0 id) 1)          -- [0]
-- Two stack primitives on top of Contender 54's seven.
#eval prims57.length                                      -- 9
