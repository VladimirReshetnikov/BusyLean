import BusyLean.Contender58
open BusyLean BusyLean.Ordinal

-- Each tower level adds two primitives on top of Contender 54's seven.
#eval (primsK 0).length                                   -- 7
#eval (primsK 3).length                                   -- 13
-- At size 0 the closure of level 2 is `m + 1 + max (g m) 0`.
#eval Ordinal.numLift (primsK 2) (envK 0 (· + 5) 2) (· + 5) 0   -- 6
