import BusyLean.Contender19
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

open LVeblen in
def z : V := .node []
open LVeblen in
def one : V := .node [.phi []]
open LVeblen in
def omega : V := .node [.phi [.entry z one]]                       -- ω = φ(1@0)
def eps0 : LargeVeblen := ⟨.node [.phi [.entry one one]], rfl⟩      -- ε₀ = φ(1@1)
def svo : LargeVeblen := ⟨.node [.phi [.entry omega one]], rfl⟩     -- φ(1@ω): small Veblen ordinal

/-- Pack `λ_ : dyn_ε₀. nat` into the universe at the small Veblen ordinal: 7. -/
def climb : CTm LargeVeblen :=
  let k : Kind LargeVeblen := .arr (.atom eps0) .star
  let A : Ty LargeVeblen := lam (.atom eps0) Ty.nat
  .app (.lam (app (.atom eps0) (aunpack svo k (apack svo k A))
      (apack eps0 .star Ty.nat)) (.var 0)) (cnum 7)

/-- The opposite direction is rejected (0). -/
def downward : CTm LargeVeblen :=
  let k : Kind LargeVeblen := .arr (.atom svo) .star
  let A : Ty LargeVeblen := lam (.atom svo) Ty.nat
  .app (.lam (app (.atom svo) (aunpack eps0 k (apack eps0 k A))
      (apack svo .star Ty.nat)) (.var 0)) (cnum 7)

#eval lvalue id 20 climb      -- 7
#eval lvalue id 20 downward   -- 0
#eval (List.range 3).map fun n => (largeVeblenUpTo n).length
