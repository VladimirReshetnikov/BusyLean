import BusyLean.Contender49
open BusyLean BusyLean.FT2 BusyLean.Ordinal Ty

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)

def body : Nat → CTm
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum (n : Nat) : CTm := .tlam (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))
def natTy : Ty := Ty.nat
/-- `succ` on Church numerals. -/
def csucc : CTm :=
  .lam natTy (.tlam (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0)
    (.app (.var 1) (.app (.app (.tapp (.var 2) (tvar 0)) (.var 1)) (.var 0))))))
/-- The height of the input tree: `trec [nat] 0 succ (λh. h 0) tin`. -/
def height : CTm :=
  .app (.app (.app (.app (.tapp .trec natTy) (cnum 0)) csucc)
    (.lam (arr natTy natTy) (.app (.var 0) (cnum 0)))) .tin

#eval natValue ⟨id, fin 7⟩ height                       -- 7: the program reads the tree
#eval natValue ⟨id, fin 2⟩ (.app .orc (cnum 3))         -- 3: the number oracle
