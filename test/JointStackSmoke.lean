import BusyLean.Contender56
open BusyLean.Ordinal
open BusyLean.Ordinal.TL (Ty)

def P : List Ty := []
def σ : TL.Env P := ()

-- At size 0 no programs are enumerated, at every level of the joint stack.
#eval (jointStack P σ .zero).2 (fun n => n + 5) 0                -- 6
#eval (jointStack P σ (.succ .zero)).2 (fun n => n + 5) 0        -- 6
#eval (jointStack P σ (.lim fun _ => .zero)).2 (fun n => n + 5) 0  -- 6
