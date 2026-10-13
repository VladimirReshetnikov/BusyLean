import BusyLean.Contender16
open BusyLean.FL BusyLean.Ordinal Ty

def body {α : Type} : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum {α : Type} (n : Nat) : CTm α :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

def three : OmegaPow := ⟨[0, 0, 0], rfl⟩   -- ω⁰+ω⁰+ω⁰ = 3
def omega : OmegaPow := ⟨[1], rfl⟩         -- ω

/-- Pack `λ_ : dyn_3. nat` (kind `dyn_3 → ★`) into the level-ω universe, read it
back, and apply it to a packed `nat` at level 3: evaluates to 4. -/
def climbOmega : CTm OmegaPow :=
  let k : Kind OmegaPow := .arr (.atom three) .star
  let A : Ty OmegaPow := lam (.atom three) Ty.nat
  .app (.lam (app (.atom three) (aunpack omega k (apack omega k A))
      (apack three .star Ty.nat)) (.var 0)) (cnum 4)

/-- Level 3 cannot hold an operator over level ω (rejected, 0). -/
def downward : CTm OmegaPow :=
  let k : Kind OmegaPow := .arr (.atom omega) .star
  let A : Ty OmegaPow := lam (.atom omega) Ty.nat
  .app (.lam (app (.atom omega) (aunpack three k (apack three k A))
      (apack omega .star Ty.nat)) (.var 0)) (cnum 4)

#eval tvalue id 20 climbOmega     -- 4
#eval tvalue id 20 downward       -- 0
#eval (omegaPowUpTo 3).map (·.1)  -- notations below ω^ω with ≤ 3 terms, exponents < 3
#eval (List.range 3).map fun n => (transfiniteUpTo n).length
