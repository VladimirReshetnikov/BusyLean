import BusyLean.Contender14
open BusyLean.FL Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

/-- Level 1: `(λx : aunpack dyn₀ ★ (apack dyn₀ ★ nat). x) 3̄`. -/
def viaAtom : CTm (Atom 1) :=
  .app (.lam (aunpack (Atom.new 0) .star (apack (Atom.new 0) .star Ty.nat)) (.var 0)) (cnum 3)

/-- Level 2: pack into `dyn₁` at the kind `dyn₀ → ★`, which lies below it. -/
def climb : CTm (Atom 2) :=
  let k : Kind (Atom 2) := .arr (.atom (Atom.old (Atom.new 0))) .star
  let A : Ty (Atom 2) := lam (.atom (Atom.old (Atom.new 0))) Ty.nat
  .app (.lam (app (.atom (Atom.old (Atom.new 0))) (aunpack (Atom.new 1) k (apack (Atom.new 1) k A))
      (apack (Atom.old (Atom.new 0)) .star Ty.nat)) (.var 0)) (cnum 4)

/-- An atom cannot hold its own kind (rejected, 0). -/
def selfPack : CTm (Atom 1) :=
  .app (.lam (aunpack (Atom.new 0) (.atom (Atom.new 0))
      (apack (Atom.new 0) (.atom (Atom.new 0)) (apack (Atom.new 0) .star Ty.nat))) (.var 0)) (cnum 2)

#eval fvalue 1 id 10 viaAtom     -- 3
#eval fvalue 1 id 0 viaAtom      -- 0: the conversion needs fuel
#eval fvalue 2 id 20 climb       -- 4
#eval fvalue 1 id 10 selfPack    -- 0
#eval fvalue 0 (· + 7) 10 (.app .orc (cnum 3))  -- 10
#eval (List.range 3).map fun n => (ladderUpTo n).length
