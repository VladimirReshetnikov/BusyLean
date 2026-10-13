import BusyLean.Contender46
open BusyLean BusyLean.Ordinal

def succs : CTree → Nat
  | .succ t => succs t + 1
  | _ => 0

def branch (i : Nat) : CTree → CTree
  | .lim f => f i
  | t => t

def J3 (t : CTree) : CTree := .succ (.succ (.succ t))

-- At the countable level, a successor step of `DNJ` applies `J` on branch 1.
#eval succs (branch 1 (U2.DNJ U2.Univ.base J3 .zero (.succ .zero)))   -- 3
