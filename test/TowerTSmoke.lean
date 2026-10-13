import BusyLean.Contender59
open BusyLean.Ordinal
open BusyLean.Ordinal.TL (Ty)

def P : List Ty := []
def σ : TL.Env P := ()

-- At size 0 no programs are enumerated at any level of the tower.
#eval (towerT P σ .zero).2 (fun n => n + 5) 0                     -- 6
#eval (towerT P σ (.succ (.succ .zero))).2 (fun n => n + 5) 0     -- 6
-- `jointFrom` starts from the given closure pair.
#eval (jointFrom P σ (fun _ t => t, fun g m => g m + 100) .zero).2 (fun n => n) 1   -- 101
