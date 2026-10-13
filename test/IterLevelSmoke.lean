import BusyLean.Contender48
open BusyLean BusyLean.Ordinal

def succs : CTree → Nat
  | .succ t => succs t + 1
  | _ => 0

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)

/-- A toy `Φ`: run `B` once more per successor of the height. -/
def toyΦ (B : CTree → CTree) : CTree → CTree → CTree
  | .succ a => fun t => B (toyΦ B a t)
  | _ => B

-- iterOf at height zero is the base; one successor runs Φ once from the base.
#eval succs (iterOf toyΦ (fun t => .succ t) .zero (fin 2))            -- 3
#eval succs (iterOf toyΦ (fun t => .succ t) (fin 1) (fin 2))          -- 5: toyΦ succ (fin 2) (fin 2)
