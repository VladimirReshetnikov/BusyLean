import BusyLean.Contender7
open BusyLean.F Ty

/-- `X := tvar 0`; the Church numeral `ΛX. λf:X→X. λx:X. fⁿ x`. -/
def body : Nat → CTm
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum (n : Nat) : CTm := .tlam (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

/-- `exp m n = ΛX. n [X→X] (m [X])`, i.e. `m ^ n`. -/
def cexp (m n : CTm) : CTm :=
  .tlam (.app (.tapp n (arr (tvar 0) (tvar 0))) (.tapp m (tvar 0)))

-- Type inference: numerals and powers have the Church numeral type.
#eval infer [] (cnum 3) == some Ty.nat
#eval infer [] (cexp (cnum 2) (cnum 3)) == some Ty.nat
-- Values: 3, 2^3 = 8, 3^(2^2) = 81 (polymorphic instantiation at work).
#eval fvalue id (cnum 3)
#eval fvalue id (cexp (cnum 2) (cnum 3))
#eval fvalue id (cexp (cnum 3) (cexp (cnum 2) (cnum 2)))
-- The oracle: with f n = 10 n, `orc 4̄` is 40, and `orc (2^3)` is 80.
#eval fvalue (· * 10) (.app .orc (cnum 4))
#eval fvalue (· * 10) (.app .orc (cexp (cnum 2) (cnum 3)))
-- Ill-typed programs are worth 0.
#eval fvalue id (.app (cnum 2) (cnum 2))
-- Enumeration sizes and small reflections.
#eval (List.range 4).map fun n => (ctmsUpTo n).length
#eval (List.range 4).map (reflectF (· + 1))
