import BusyLean.Contender28
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

def climb {α : Type} (lo hi : α) : CTm α :=
  let k : Kind α := .arr (.atom lo) .star
  let A : Ty α := lam (.atom lo) Ty.nat
  .app (.lam (app (.atom lo) (aunpack hi k (apack hi k A)) (apack lo .star Ty.nat)) (.var 0)) (cnum 15)

def top : Addr (roundTree 1) := TreePath.root
def below : Addr (roundTree 1) := TreePath.child (TreePath.child TreePath.root 3) 5

#eval TreePath.valid (roundTree 1) (TreePath.child (TreePath.child TreePath.root 3) 5)   -- true
#eval rtvalue 1 id 20 (climb below top)    -- 15: a descendant's universe packs into the root's
#eval rtvalue 1 id 20 (climb top below)    -- 0: the root's kind does not fit below
#eval (List.range 4).map fun n => (addrUpTo (roundTree n) n).length
