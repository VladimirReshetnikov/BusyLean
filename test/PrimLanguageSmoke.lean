import BusyLean.Contender51
open BusyLean.Ordinal BusyLean.Ordinal.PTL
open BusyLean.Ordinal.TL (Ty)

def succs : CTree → Nat
  | .succ t => succs t + 1
  | _ => 0

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)

def P : List Ty := [.tree, .arr .tree .tree]
def σ : TL.Env P := (fin 2, fun t => .succ t, ())

def run (r : Raw) : Nat :=
  match infer P [] r with
  | some ⟨.tree, t⟩ => succs (t.eval σ ())
  | _ => 0

#eval run (.app (.prim 1) (.prim 0))                                   -- 3
-- treeRec over the seed at type tree: replace every successor by two.
#eval run (.treeRec .tzero (.lam .tree (.tsucc (.tsucc (.var 0))))
  (.lam (.arr .nat .tree) (.tlim (.var 0))) (.prim 0))                 -- 4
#eval run (.prim 5)                                                    -- 0: no such primitive
