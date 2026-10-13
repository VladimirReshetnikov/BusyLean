import BusyLean.Contender22
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

/-- Two atoms of `tower 2`: a base atom (the level-0 term `0` of `tower 1`), and the
collapse `ψ₀` of that atom, which lies above every base atom. -/
def baseZero : (tower 1).T := ⟨0, ⟨.node [], rfl⟩⟩
def atomLow : (tower 2).T := ⟨0, ⟨.node [.B baseZero], rfl⟩⟩
def atomHigh : (tower 2).T := ⟨0, ⟨.node [.D 0 (.node [.B baseZero])], rfl⟩⟩

def climb : CTm (tower 2).T :=
  let k : Kind (tower 2).T := .arr (.atom atomLow) .star
  let A : Ty (tower 2).T := lam (.atom atomLow) Ty.nat
  .app (.lam (app (.atom atomLow) (aunpack atomHigh k (apack atomHigh k A))
      (apack atomLow .star Ty.nat)) (.var 0)) (cnum 10)

def downward : CTm (tower 2).T :=
  let k : Kind (tower 2).T := .arr (.atom atomHigh) .star
  let A : Ty (tower 2).T := lam (.atom atomHigh) Ty.nat
  .app (.lam (app (.atom atomHigh) (aunpack atomLow k (apack atomLow k A))
      (apack atomHigh .star Ty.nat)) (.var 0)) (cnum 10)

#eval tvalue22 2 id 20 climb      -- 10
#eval tvalue22 2 id 20 downward   -- 0
