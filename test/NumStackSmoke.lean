import BusyLean.Contender55
open BusyLean.Ordinal
open BusyLean.Ordinal.TL (Ty)

def P : List Ty := []
def σ : TL.Env P := ()

-- At size 0 no programs are enumerated: numLift [] () g 0 = 0 + 1 + max (g 0) 0.
#eval numLift P σ (fun n => n + 5) 0                       -- 6
#eval numStack P σ .zero (fun n => n + 5) 0                -- 6
-- One level up: the oracle of numLift is the closure functional's input `g`.
#eval numStack P σ (.succ .zero) (fun n => n + 5) 0        -- 6
