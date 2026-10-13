import BusyLean.Contender47
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

-- `thetaFrom` at index zero is its base; `psi` at zero is the meta-jump.
#eval succs (thetaFrom 0 (fun t => .succ t) .zero (fin 2))                 -- 3
#eval succs (branch 0 (branch 0 (branch 0 (psi 0 .zero (fin 4)))))          -- 4
