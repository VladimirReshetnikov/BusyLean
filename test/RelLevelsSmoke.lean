import BusyLean.Contender44
open BusyLean.Ordinal

def succs : CTree → Nat
  | .succ t => succs t + 1
  | _ => 0

def branch (i : Nat) : CTree → CTree
  | .lim f => f i
  | t => t

def J3 (t : CTree) : CTree := .succ (.succ (.succ t))

-- Level-0 successor steps of `DLJ` apply `J` on branch 1.
#eval succs (branch 1 (DLJ J3 .zero (.succ .zero)))           -- 3
-- Branch 0 of a round is the previous tree.
#eval succs (branch 0 (relLevelRounds J3 1 (J3 .zero)))       -- 3
