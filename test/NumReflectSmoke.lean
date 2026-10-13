import BusyLean.Contender54
open BusyLean.Ordinal BusyLean.Ordinal.PTL
open BusyLean.Ordinal.TL (Ty)

-- A toy environment: a number oracle `g n = 3 n + 1` only.
def P : List Ty := [.arr .nat .nat]
def σ : TL.Env P := (fun (n : Nat) => 3 * n + 1, ())

-- Closed `nat` programs of size ≤ 2: `zero`, `g zero`, `succ zero`, `natRec zero g zero`.
-- (Size 3 already enumerates far too many raw terms to run here.)
#eval natsUpTo P σ 2                       -- [0, 1, 1, 0]
