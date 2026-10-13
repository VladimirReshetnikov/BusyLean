import BusyLean.Contender40
open BusyLean BusyLean.Ordinal

def probe : CTree → Nat
  | .succ t => probe t + 1
  | .lim f => probe (f 0)
  | _ => 0

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)

-- Branch 0 of the FT2 jump is its input; branch 0 of `base40` is the jump.
#eval probe (base40 0 (fin 4))                 -- 4
#eval hier Nat.succ (FT2.jumpF id 0 (fin 2)) 1  -- 7: max over branches (fin 2, padding)
