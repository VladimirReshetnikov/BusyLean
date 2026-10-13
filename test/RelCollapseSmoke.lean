import BusyLean.Contender42
open BusyLean.Ordinal

def succs : CTree → Nat
  | .succ t => succs t + 1
  | _ => 0

def branch (i : Nat) : CTree → CTree
  | .lim f => f i
  | t => t

def J3 (t : CTree) : CTree := .succ (.succ (.succ t))

-- `DJ J 0 (t+1) = lim (ε⁺ x, J (ε⁺ x))`: branch 1 of one successor step is `J` applied.
#eval succs (branch 1 (DJ J3 0 (.succ .zero)))               -- 3
#eval succs (branch 1 (DJ J3 0 (.succ (.succ .zero))))       -- 3
-- Do not run `hier` on these trees at small arguments: ε-numbers make it astronomically slow.
