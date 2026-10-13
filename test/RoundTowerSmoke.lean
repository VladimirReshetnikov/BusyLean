import BusyLean.Contender24
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

/-- Pack `λ_ : dyn_lo. nat` into the universe at `hi` and use it. -/
def climb {α : Type} (lo hi : α) : CTm α :=
  let k : Kind α := .arr (.atom lo) .star
  let A : Ty α := lam (.atom lo) Ty.nat
  .app (.lam (app (.atom lo) (aunpack hi k (apack hi k A)) (apack lo .star Ty.nat)) (.var 0)) (cnum 11)

/-- The first ordered pair of distinct atoms of `roundTower 1` in the depth-2 enumeration. -/
def pair : Option ((roundTower 1).T × (roundTower 1).T) :=
  let as := (roundTower 1).enum 2
  as.findSome? fun a => (as.find? fun b => (roundTower 1).lt a b).map fun b => (a, b)

#eval ((roundTower 1).enum 2).length                                   -- atoms available
#eval pair.map fun (lo, hi) => rvalue 1 id 20 (climb lo hi)            -- some 11
#eval pair.map fun (lo, hi) => rvalue 1 id 20 (climb hi lo)            -- some 0 (downward)
