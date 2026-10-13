import BusyLean.Contender61
open BusyLean BusyLean.Ordinal BusyLean.Ordinal.PTL2

def P : List Ty := [.arr .nat .nat]
def σ : Env P := (fun (n : Nat) => 3 * n + 1, ())

def runNat (r : Raw) : Nat :=
  match infer P [] r with
  | some ⟨.nat, t⟩ => t.eval σ ()
  | _ => 0

#eval runNat (.snd (.pair .zero (.app (.prim 0) (.succ .zero))))     -- 4
#eval runNat (.fst (.pair (.succ .zero) .tzero))                    -- 1
-- The tower primitive applied to the seed has the closure-pair type.
#eval ((infer prims61 [] (.app (.prim 4) (.prim 0))).map (·.1)) == some closTy   -- true
-- towerH maps families to families.
#eval ((infer prims61 [] (.app (.prim 5) (.prim 4))).map (·.1)) == some famTy    -- true
