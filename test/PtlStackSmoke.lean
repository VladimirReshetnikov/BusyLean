import BusyLean.Contender52
open BusyLean.Ordinal
open BusyLean.Ordinal.TL (Ty)

def succs : CTree → Nat
  | .succ t => succs t + 1
  | _ => 0

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)

def P : List Ty := [.tree]
def σ : TL.Env P := (fin 2, ())

-- Closed `tree → tree` programs of size ≤ 2 over [lift-free] primitives `b`, seed:
-- `b` itself, `λ_. seed` and `λ_. 0` (variables appear from size 3).
#eval (PTL.funsUpTo (.arr .tree .tree :: P) ((fun t => .succ t), σ) 2).length   -- 3
#eval ((PTL.funsUpTo (.arr .tree .tree :: P) ((fun t => .succ t), σ) 2).map
  (fun f => succs (f (fin 3))))                                                 -- [4, 2, 0]
