import BusyLean.Contender45
open BusyLean BusyLean.Ordinal

def succs : CTree → Nat
  | .succ t => succs t + 1
  | _ => 0

def branch (i : Nat) : CTree → CTree
  | .lim f => f i
  | t => t

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)

-- Θ at a limit index is a limit of the stages; branch 0 of Θ_0 (the meta-jump) is
-- Contender 41's base, whose branch 0 is the ladder jump, whose branch 0 is the input.
#eval succs (branch 0 (branch 0 (branch 0 (theta 0 .zero (fin 4)))))   -- 4
