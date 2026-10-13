import BusyLean.Contender21
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

def psiOmega2 : Buchholz 2 := ⟨.node [.D 0 (.node [.D 2 (.node [])])], rfl⟩   -- ψ₀(Ω₂)
def omega1 : Buchholz 2 := ⟨.node [.D 1 (.node [])], rfl⟩                      -- Ω₁

/-- Pack `λ_ : dyn_{ψ₀(Ω₂)}. nat` into the universe at `Ω₁` and use it: 9. -/
def climb : CTm (Buchholz 2) :=
  let k : Kind (Buchholz 2) := .arr (.atom psiOmega2) .star
  let A : Ty (Buchholz 2) := lam (.atom psiOmega2) Ty.nat
  .app (.lam (app (.atom psiOmega2) (aunpack omega1 k (apack omega1 k A))
      (apack psiOmega2 .star Ty.nat)) (.var 0)) (cnum 9)

/-- The opposite direction is rejected (0). -/
def downward : CTm (Buchholz 2) :=
  let k : Kind (Buchholz 2) := .arr (.atom omega1) .star
  let A : Ty (Buchholz 2) := lam (.atom omega1) Ty.nat
  .app (.lam (app (.atom omega1) (aunpack psiOmega2 k (apack psiOmega2 k A))
      (apack omega1 .star Ty.nat)) (.var 0)) (cnum 9)

#eval zvalue 2 id 20 climb      -- 9
#eval zvalue 2 id 20 downward   -- 0
#eval (List.range 4).map fun n => (buchholzUpTo n n).length
