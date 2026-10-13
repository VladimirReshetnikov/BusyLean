import BusyLean.Contender62
open BusyLean.Ordinal
open BusyLean.Ordinal.PTL2 (Ty Env)

def P : List Ty := []
def σ : Env P := ()

-- At size 0 no programs are enumerated, at every level of the stack.
#eval (stack2 P σ .zero).2 (fun n => n + 5) 0                      -- 6
#eval (stack2 P σ (.succ (.succ .zero))).2 (fun n => n + 5) 0      -- 6
