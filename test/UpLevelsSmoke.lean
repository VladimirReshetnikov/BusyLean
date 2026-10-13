import BusyLean.Contender60
open BusyLean.Ordinal
open BusyLean.Ordinal.TL (Ty)

def P : List Ty := []
def σ : TL.Env P := ()

-- At size 0 no programs are enumerated at any level or height.
#eval (upLevels P σ .zero (.succ .zero)).2 (fun n => n + 5) 0                -- 6
#eval (upLevels P σ (.succ .zero) (.succ (.succ .zero))).2 (fun n => n + 5) 0  -- 6
