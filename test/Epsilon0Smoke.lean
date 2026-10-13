import BusyLean.Contender17
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

def z : Cnf := .node []
def omega : Epsilon0 := ⟨.node [.node [z]], rfl⟩            -- ω
def omegaOmega : Epsilon0 := ⟨.node [.node [.node [z]]], rfl⟩  -- ω^ω

/-- Pack `λ_ : dyn_ω. nat` into the level-ω^ω universe and use it: 5. -/
def climb : CTm Epsilon0 :=
  let k : Kind Epsilon0 := .arr (.atom omega) .star
  let A : Ty Epsilon0 := lam (.atom omega) Ty.nat
  .app (.lam (app (.atom omega) (aunpack omegaOmega k (apack omegaOmega k A))
      (apack omega .star Ty.nat)) (.var 0)) (cnum 5)

/-- The opposite direction is rejected (0). -/
def downward : CTm Epsilon0 :=
  let k : Kind Epsilon0 := .arr (.atom omegaOmega) .star
  let A : Ty Epsilon0 := lam (.atom omegaOmega) Ty.nat
  .app (.lam (app (.atom omegaOmega) (aunpack omega k (apack omega k A))
      (apack omegaOmega .star Ty.nat)) (.var 0)) (cnum 5)

#eval evalue id 20 climb      -- 5
#eval evalue id 20 downward   -- 0
#eval (List.range 5).map fun n => (epsilon0UpTo n).length
