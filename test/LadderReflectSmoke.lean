import BusyLean.Contender50
open BusyLean BusyLean.FLT2 BusyLean.Ordinal
open BusyLean.FL (Kind Ty)
open BusyLean.FL.Ty

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)

section
variable {α : Type}
def body : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum (n : Nat) : CTm α := .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))
def csucc : CTm α :=
  .lam Ty.nat (.tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0)
    (.app (.var 1) (.app (.app (.tapp (.var 2) (tvar 0)) (.var 1)) (.var 0))))))
/-- `ΛX. λrec x. rec [nat] 0 succ (λh. h 0) x`: the height of the input. -/
def height : CTm α :=
  .tlam .star (.lam recTy (.lam (tvar 0)
    (.app (.app (.app (.app (.tapp (.var 1) Ty.nat) (cnum 0)) csucc)
      (.lam (arr Ty.nat Ty.nat) (.app (.var 0) (cnum 0)))) (.var 0))))
end

#eval readNat id (fin 6) 60 height     -- 6
