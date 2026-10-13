import BusyLean.SystemFT2.Trees
open BusyLean.FT2 BusyLean.Ordinal Ty

/-- Follows successors and branch 5 of limits. -/
def probe : CTree → Nat
  | .succ t => probe t + 1
  | .lim f => probe (f 5)
  | _ => 0

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)
def omegaT : CTree := .lim fin

/-- `trec [tree] z s l tin`. -/
def recIn (z s l : CTm) : CTm := .app (.app (.app (.app (.tapp .trec Ty.tree) z) s) l) .tin
def limId : CTm := .lam (arr Ty.nat Ty.tree) (.app (.con 2) (.var 0))
/-- Doubles every successor of the input tree. -/
def double : CTm := recIn (.con 0) (.lam Ty.tree (.app (.con 1) (.app (.con 1) (.var 0)))) limId

#eval probe (progTree ⟨id, fin 3⟩ .tin)       -- 3: the input tree itself
#eval probe (progTree ⟨id, fin 3⟩ double)     -- 6
#eval probe (progTree ⟨id, omegaT⟩ double)    -- 10: branch 5 of ω, doubled
#eval probe (progTree ⟨id, omegaT⟩ (recIn (.con 0) (.lam Ty.tree (.var 0)) limId))  -- 0
