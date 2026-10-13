import BusyLean.Contender35
open BusyLean.FT BusyLean.Ordinal Ty

/-- Follows successors and branch 5 of limits. -/
def probe : CTree → Nat
  | .succ t => probe t + 1
  | .lim f => probe (f 5)
  | _ => 0

def natTy : Ty := all (arr (arr (tvar 0) (tvar 0)) (arr (tvar 0) (tvar 0)))
def body : Nat → CTm
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum (n : Nat) : CTm := .tlam (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

/-- A Church numeral (a numeral, or a variable of type nat) run at `tree`. -/
def toT (e : CTm) : CTm := .app (.app (.tapp e Ty.tree) (.con 1)) (.con 0)

#eval probe (progTree id (.app (.con 1) (.app (.con 1) (.con 0))))       -- 2
#eval probe (progTree id (toT (cnum 3)))                                 -- 3
#eval probe (progTree id (.app (.con 2) (.lam natTy (toT (.var 0)))))    -- 5
#eval probe (progTree (· * 2) (.app (.con 2) (.lam natTy (toT (.app .orc (.var 0))))))  -- 10
#eval probe (progTree id (.app (.con 1) .orc))                           -- 0 (ill-typed)

#print axioms BusyLean.FT.progTree
