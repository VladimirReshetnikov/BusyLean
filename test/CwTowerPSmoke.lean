import BusyLean.Contender69
open BusyLean BusyLean.Ordinal
open BusyLean.Ordinal.PTL2 (Ty Env)

def P : List Ty := []
def σ : Env P := ()
def H : CTree → Closures := fun _ => (fun _ t => t, fun g m => g m)

-- At size 0 no programs are enumerated at any level, for any family.
#eval (cwTowerP P σ .zero H).2 (fun n => n + 5) 0                 -- 6
#eval (cwTowerP P σ (.succ (.succ .zero)) H).2 (fun n => n + 5) 0  -- 6
