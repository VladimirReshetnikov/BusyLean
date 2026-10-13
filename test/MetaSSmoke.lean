import BusyLean.Contender65
open BusyLean BusyLean.Ordinal

-- `towerFrom` at height zero is its starting pair; a successor applies the step.
def c0 : Closures := (fun _ t => t, fun g m => g m + 100)
def S : Closures → Closures := fun c => (c.1, fun g m => c.2 g m + 1)
#eval (towerFrom S c0 .zero).2 (fun n => n) 1                    -- 101
#eval (towerFrom S c0 (.succ (.succ .zero))).2 (fun n => n) 1    -- 103
