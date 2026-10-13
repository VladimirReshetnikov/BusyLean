import BusyLean.Contender10
open BusyLean.Fk Ty

def body : Nat → CTm
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum (n : Nat) : CTm :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))
def cexp (m n : CTm) : CTm :=
  .tlam .star (.app (.tapp n (arr (tvar 0) (tvar 0))) (.tapp m (tvar 0)))

/-- A kind-polymorphic function: `Λκ. ΛF:κ. λx:nat. x`,
of type `∀κ. ∀F:κ. nat → nat`. -/
def kpoly : CTm := .klam (.tlam (.kvar 0) (.lam Ty.nat (.var 0)))

def IdOp : Ty := lam .star (tvar 0)

/-- Used at kind `★` with `nat`, and at kind `★ → ★` with `λX. X`. -/
def atStar : CTm := .app (.tapp (.kapp kpoly .star) Ty.nat) (cnum 4)
def atArrow : CTm := .app (.tapp (.kapp kpoly (.arr .star .star)) IdOp) (cnum 6)
/-- Ill-kinded: `λX. X` is not of kind `★`. -/
def illKinded : CTm := .app (.tapp (.kapp kpoly .star) IdOp) (cnum 6)

#eval infer 10 [] [] kpoly == some (kall (all (.kvar 0) (arr Ty.nat Ty.nat)))  -- true
#eval fvalue id 10 atStar           -- 4
#eval fvalue id 10 atArrow          -- 6
#eval fvalue id 10 illKinded        -- 0 (rejected)
#eval fvalue id 10 (cexp (cnum 2) (cnum 5))   -- 32
#eval fvalue (· * 3) 10 (.app .orc (cnum 5))  -- 15
#eval (List.range 4).map fun n => (ctmsUpTo n).length
