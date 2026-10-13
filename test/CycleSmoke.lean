import BusyLean.Contender70
open BusyLean BusyLean.Ordinal

-- Each cycle adds the step and the tower as two primitives on top of Contender 66's eight.
#eval (primsR 0).length                 -- 8
#eval (primsR 3).length                 -- 14
-- The first cycle reproduces Contender 68's primitive types.
#eval primsR 1 == prims68               -- true
