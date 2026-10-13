import BusyLean.Contender36
open BusyLean.FLT BusyLean.Ordinal
open BusyLean.FL (Kind Ty)
open BusyLean.FL.Ty

/-- Follows successors and branch 5 of limits. -/
def probe : CTree → Nat
  | .succ t => probe t + 1
  | .lim f => probe (f 5)
  | _ => 0

def t1 : CTree := .succ .zero
abbrev A := Addr t1
/-- `ΛX. λz s l. body` at the Church tree type. -/
def church (body : CTm A) : CTm A :=
  .tlam .star (.lam (tvar 0) (.lam (arr (tvar 0) (tvar 0))
    (.lam (arr (arr Ty.nat (tvar 0)) (tvar 0)) body)))

def two : CTm A := church (.app (.var 1) (.app (.var 1) (.var 2)))
/-- `l (λn:nat. n [X] s z)`: the limit of the finite trees. -/
def omegaT : CTm A := church (.app (.var 0)
  (.lam Ty.nat (.app (.app (.tapp (.var 0) (tvar 0)) (.var 2)) (.var 3))))

#eval probe (progTree id t1 30 two)      -- 2
#eval probe (progTree id t1 30 omegaT)   -- 5
#eval probe (progTree id t1 30 .orc)     -- 0 (wrong type)
-- Branch 0 of a bootstrap step is the tree itself.
def branch0 : CTree → CTree
  | .lim g => g 0
  | t => t
#eval probe (branch0 (ladderTree id 0 (.succ (.succ .zero))))   -- 2
