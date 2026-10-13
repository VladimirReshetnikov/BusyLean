import BusyLean.Contender53
open BusyLean BusyLean.Ordinal

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)

-- At depth 0 no programs are enumerated: treeReflect id T 0 = 0 + 1 + max(0, 0) = 1,
-- and ladderReflect id T 0 = 0 + 1 + max(1, 0) = 2.
#eval reflAlong (fin 1) id .zero 0          -- 0 (the base)
#eval reflAlong (fin 1) id (fin 1) 0        -- 2
#eval reflAlong (fin 1) id (fin 2) 0        -- 0 + 1 + max(0 + 1 + max(2, 0), 0) = 4
