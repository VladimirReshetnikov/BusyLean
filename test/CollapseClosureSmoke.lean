import BusyLean.Contender43
open BusyLean BusyLean.Ordinal

def succs : CTree → Nat
  | .succ t => succs t + 1
  | _ => 0

def J3 (t : CTree) : CTree := .succ (.succ (.succ t))

-- Level 0 of the stack is the given closure operator.
#eval succs (metaBoostC (fun J t => J t) .zero J3 .zero)      -- 3
-- Branch 1 of `closeC` is the relative collapse; its root is a limit (`Ω`-free level 0).
#eval match closeC 0 J3 .zero with | .lim _ => "lim" | _ => "other"   -- lim
