import BusyLean.Contender20
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

def psiOmega : BachmannHoward := ⟨.node [.D false (.node [.D true (.node [])])], rfl⟩  -- ψ₀(Ω)
def bigOmega : BachmannHoward := ⟨.node [.D true (.node [])], rfl⟩                     -- Ω

/-- Pack `λ_ : dyn_{ψ₀(Ω)}. nat` into the universe at `Ω` and use it: 8. -/
def climb : CTm BachmannHoward :=
  let k : Kind BachmannHoward := .arr (.atom psiOmega) .star
  let A : Ty BachmannHoward := lam (.atom psiOmega) Ty.nat
  .app (.lam (app (.atom psiOmega) (aunpack bigOmega k (apack bigOmega k A))
      (apack psiOmega .star Ty.nat)) (.var 0)) (cnum 8)

/-- The opposite direction is rejected (0). -/
def downward : CTm BachmannHoward :=
  let k : Kind BachmannHoward := .arr (.atom bigOmega) .star
  let A : Ty BachmannHoward := lam (.atom bigOmega) Ty.nat
  .app (.lam (app (.atom bigOmega) (aunpack psiOmega k (apack psiOmega k A))
      (apack bigOmega .star Ty.nat)) (.var 0)) (cnum 8)

#eval bvalue id 20 climb      -- 8
#eval bvalue id 20 downward   -- 0
#eval (List.range 4).map fun n => (bachmannHowardUpTo n).length
