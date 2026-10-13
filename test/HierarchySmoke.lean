import BusyLean.Contender38
open BusyLean.Ordinal

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)
def omegaT : CTree := .lim fin

#eval hier Nat.succ .zero 3              -- 4
#eval hier Nat.succ (fin 1) 3            -- 3 + 4 = 7
#eval hier Nat.succ (fin 2) 2            -- iterate (x ↦ 2x+1-ish) : 23
#eval hier Nat.succ omegaT 2             -- = hier succ (fin 2) 2 = 23
-- Padding branches with zero does not lower a limit: the maximum is taken.
#eval hier Nat.succ (.lim fun i => if i = 1 then fin 2 else .zero) 2   -- 23
