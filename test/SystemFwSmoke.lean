import BusyLean.Contender8
open BusyLean.Fw Ty

def body : Nat → CTm
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
/-- `ΛX:★. λf:X→X. λx:X. fⁿ x`. -/
def cnum (n : Nat) : CTm :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))
/-- `m ^ n` via instantiation at `X → X`. -/
def cexp (m n : CTm) : CTm :=
  .tlam .star (.app (.tapp n (arr (tvar 0) (tvar 0))) (.tapp m (tvar 0)))

/-- The identity type operator `λX:★. X`. -/
def IdOp : Ty := lam .star (tvar 0)

/-- `(λx : IdOp nat. x) 3̄`: type checks only through type-level β. -/
def viaId : CTm := .app (.lam (app .star IdOp Ty.nat) (.var 0)) (cnum 3)

/-- A program polymorphic over a type *operator*:
`(ΛF:★→★. λx:F nat. x) [IdOp] 5̄`. -/
def opPoly : CTm :=
  .app (.tapp (.tlam (.arr .star .star) (.lam (app .star (tvar 0) Ty.nat) (.var 0))) IdOp) (cnum 5)

#eval infer 10 [] [] (cexp (cnum 2) (cnum 3)) == some Ty.nat
#eval fvalue id 10 (cexp (cnum 3) (cnum 3))                 -- 27
#eval infer 10 [] [] viaId == some Ty.nat                    -- needs IdOp nat ≡ nat
#eval fvalue id 10 viaId                                     -- 3
#eval fvalue id 0 viaId                                      -- no fuel: rejected, 0
#eval fvalue id 10 opPoly                                    -- 5, via ∀F:★→★
#eval fvalue (· + 100) 10 (.app .orc (cnum 2))               -- oracle: 102
#eval (List.range 4).map fun n => (ctmsUpTo n).length
