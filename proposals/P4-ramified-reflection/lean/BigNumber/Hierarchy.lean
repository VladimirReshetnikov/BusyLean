import BigNumber.Language

/-! Ramified reflection and higher-type diagonalization. No contestant is imported. -/
namespace BigNumber

/-- The recursion is on a W-tree; the oracle only evaluates immediate children. -/
def reflect : Tree → Nat → Nat
  | .zero, n => Language.envelope (fun _ _ => 0) (n + 4)
  | .sup f, n => Language.envelope (fun i x => reflect (f i) x) (n + 4)

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

def step (a : Tree) : Tree := .sup (fun _ => a)

def Level : Nat → Type
  | 0 => Tree
  | n + 1 => Level n → Level n

def supLevel : (k : Nat) → (Nat → Level k) → Level k
  | 0, f => Tree.sup f
  | k + 1, f => fun x => supLevel k (fun n => f n x)

/-- Countable iteration lifted to any finite type level. -/
def omegaLevel (k : Nat) : Level (k + 2) :=
  fun f x => supLevel k (fun n => iterate f n x)

def seed (a : Tree) (s : Tree → Tree) : (k : Nat) → Level k
  | 0 => a
  | 1 => s
  | k + 2 => omegaLevel k

def collapse (a : Tree) (s : Tree → Tree) : (k : Nat) → Level k → Tree
  | 0, x => x
  | k + 1, f => collapse a s k (f (seed a s k))

def high (a : Tree) (s : Tree → Tree) (k : Nat) : Tree :=
  collapse a s (k + 2) (omegaLevel k)

/-- Branch zero retains the parent; later branches feed semantic values into type levels. -/
def boost (a : Tree) : Tree :=
  Tree.sup (fun
    | 0 => a
    | k + 1 => high a step (reflect a (k + 64)))

/-- Diagonalizes over every finite higher-type level with the feedback step. -/
def grandIndex : Tree :=
  Tree.sup (fun k => high Tree.zero boost k)

end BigNumber
