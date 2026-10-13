import BusyLean.Contender41
open BusyLean.FLT2 BusyLean.Ordinal
open BusyLean.FL (Kind Ty)
open BusyLean.FL.Ty

def probe : CTree → Nat
  | .succ t => probe t + 1
  | .lim f => probe (f 5)
  | _ => 0

def fin : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (fin k)
def omegaT : CTree := .lim fin

/-- `ΛX. λz s l rec input. rec [X] z (λx. s (s x)) l input`: doubles every successor. -/
def double (T : CTree) : CTm (Addr T) :=
  .tlam .star (.lam (tvar 0) (.lam (arr (tvar 0) (tvar 0))
    (.lam (arr (arr Ty.nat (tvar 0)) (tvar 0)) (.lam recTy (.lam (tvar 0)
      (.app (.app (.app (.app (.tapp (.var 1) (tvar 0)) (.var 4))
        (.lam (tvar 0) (.app (.var 4) (.app (.var 4) (.var 0))))) (.var 2)) (.var 0)))))))

#eval probe (readTree id (fin 3) 40 (double (fin 3)))    -- 6
#eval probe (readTree id omegaT 40 (double omegaT))      -- 10
