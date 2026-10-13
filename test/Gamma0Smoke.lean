import BusyLean.Contender18
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

def z : Veblen.V := .node []
def phi (a b : Veblen.V) : Veblen.V := .node [.phi a b]
def eps0 : Gamma0 := ⟨phi (phi z z) z, rfl⟩                 -- φ(1,0) = ε₀
def bigPhi : Gamma0 := ⟨phi (phi (phi z z) z) z, rfl⟩      -- φ(ε₀,0)

/-- Pack `λ_ : dyn_ε₀. nat` into the level-φ(ε₀,0) universe and use it: 6. -/
def climb : CTm Gamma0 :=
  let k : Kind Gamma0 := .arr (.atom eps0) .star
  let A : Ty Gamma0 := lam (.atom eps0) Ty.nat
  .app (.lam (app (.atom eps0) (aunpack bigPhi k (apack bigPhi k A))
      (apack eps0 .star Ty.nat)) (.var 0)) (cnum 6)

/-- The opposite direction is rejected (0). -/
def downward : CTm Gamma0 :=
  let k : Kind Gamma0 := .arr (.atom bigPhi) .star
  let A : Ty Gamma0 := lam (.atom bigPhi) Ty.nat
  .app (.lam (app (.atom bigPhi) (aunpack eps0 k (apack eps0 k A))
      (apack bigPhi .star Ty.nat)) (.var 0)) (cnum 6)

#eval gvalue id 20 climb      -- 6
#eval gvalue id 20 downward   -- 0
#eval (List.range 4).map fun n => (gamma0UpTo n).length
