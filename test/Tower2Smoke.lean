import BusyLean.Contender64
open BusyLean BusyLean.Ordinal
open BusyLean.Ordinal.PTL2 (Ty Env)

def P : List Ty := []
def σ : Env P := ()

-- `stack2From` at height zero is its starting pair.
#eval (stack2From P σ (fun _ t => t, fun g m => g m + 100) .zero).2 (fun n => n) 1   -- 101
-- At size 0 the closures of `stack2From` at a successor height enumerate nothing.
#eval (stack2From P σ (fun _ t => t, fun g m => g m + 100) (.succ .zero)).2 (fun n => n + 5) 0   -- 6
