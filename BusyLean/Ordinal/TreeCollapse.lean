import BusyLean.Ordinal.TreeAddress

/-!
# Buchholz-style collapsing on tree ordinals

Level-`v` tree ordinals `LevT v` have suprema indexed by all lower levels
(lumped together in `LowT v`) and by level `v-1` itself:

`LevT 0 = Tre Empty Empty`, `LevT (w+1) = Tre (LowT w) (LevT w)`, and
`LowT (w+1) = LowT w ⊕ LevT w`.

The argument space `TopT = Tre Empty (Σ k, LevT k)` has suprema at every
finite level. `D v : TopT → LevT v` is a family of collapsing functions,
defined by **structural recursion** with no normal forms or well-foundedness
proofs:

* `D v 0 = Ω_v` (`ω` for `v = 0`);
* `D v (t+1)` is the next ε-number above `D v t`;
* limits are mapped pointwise;
* a supremum over finite levels is split. Its part below level `v` stays a
  supremum inside `LevT v`. For every level `j ≥ v`, Buchholz's diagonal
  `x₀ = Ω_j`, `x_{n+1} = D j (g x_n)` produces the countable limit of
  `D v (g x_n)`.

The countable tree `bigTree n = D 0 (eps^n(Ω_ω + 1))`, with `Ω_ω = lim_k Ω_k`,
is heuristically `ψ₀(ε_{Ω_ω+n})`. Its rank is the length of the ladder over
`Addr (bigTree n)`, whose well-foundedness `TreeAddress` gives for free.
-/

namespace BusyLean.Ordinal

namespace Tre

variable {X Y : Type}

def nat : Nat → Tre X Y
  | 0 => .zero
  | n + 1 => .succ (nat n)

def omega : Tre X Y := .lim nat

def add (a : Tre X Y) : Tre X Y → Tre X Y
  | .zero => a
  | .succ t => .succ (add a t)
  | .lim f => .lim fun n => add a (f n)
  | .supL g => .supL fun x => add a (g x)
  | .supH g => .supH fun y => add a (g y)

def mul (a : Tre X Y) : Tre X Y → Tre X Y
  | .zero => .zero
  | .succ t => add (mul a t) a
  | .lim f => .lim fun n => mul a (f n)
  | .supL g => .supL fun x => mul a (g x)
  | .supH g => .supH fun y => mul a (g y)

/-- `ω^b`. -/
def expo : Tre X Y → Tre X Y
  | .zero => .succ .zero
  | .succ t => .lim fun n => mul (expo t) (nat n)
  | .lim f => .lim fun n => expo (f n)
  | .supL g => .supL fun x => expo (g x)
  | .supH g => .supH fun y => expo (g y)

/-- `ω^ω^⋯^x` with `k` exponentials. -/
def tower : Nat → Tre X Y → Tre X Y
  | 0, x => x
  | k + 1, x => expo (tower k x)

/-- The next ε-number above `x`. -/
def epsNext (x : Tre X Y) : Tre X Y := .lim fun k => tower k (.succ x)

/-- Change the suprema of a tree. -/
def embed {X' Y' : Type} (cL : (X → Tre X' Y') → Tre X' Y') (cH : (Y → Tre X' Y') → Tre X' Y') :
    Tre X Y → Tre X' Y'
  | .zero => .zero
  | .succ t => .succ (embed cL cH t)
  | .lim f => .lim fun n => embed cL cH (f n)
  | .supL g => cL fun x => embed cL cH (g x)
  | .supH g => cH fun y => embed cL cH (g y)

end Tre

mutual
/-- All levels below `w`, lumped together. -/
def LowT : Nat → Type
  | 0 => Empty
  | w + 1 => LowT w ⊕ LevT w
/-- Level-`w` tree ordinals. -/
def LevT : Nat → Type
  | 0 => Tre Empty Empty
  | w + 1 => Tre (LowT w) (LevT w)
end

/-- The level and element of a lumped lower index. -/
def decLow : (w : Nat) → LowT w → Σ k, LevT k
  | 0, b => b.elim
  | w + 1, .inl b => decLow w b
  | w + 1, .inr x => ⟨w, x⟩

/-- Generic constructors at every level. -/
def LevT.lim : (v : Nat) → (Nat → LevT v) → LevT v
  | 0, f => Tre.lim f
  | _ + 1, f => Tre.lim f

def LevT.zero : (v : Nat) → LevT v
  | 0 => Tre.zero
  | _ + 1 => Tre.zero

def LevT.epsNext : (v : Nat) → LevT v → LevT v
  | 0, x => Tre.epsNext x
  | _ + 1, x => Tre.epsNext x

/-- One level up. -/
def LevT.up : (w : Nat) → LevT w → LevT (w + 1)
  | 0, t => Tre.embed (fun g => .supL g) (fun g => .supL g) t
  | _ + 1, t => Tre.embed
      (fun g => .supL fun b => match b with | .inl b' => g b' | .inr _ => .zero)
      (fun g => .supL fun b => match b with | .inr x => g x | .inl _ => .zero) t

/-- `Ω_v`: `ω` at level 0, the supremum of level `v-1` otherwise. -/
def LevT.Omega : (v : Nat) → LevT v
  | 0 => Tre.omega
  | w + 1 => Tre.supH fun x => LevT.up w x

/-- Suprema below level `v`, kept inside `LevT v`. -/
def LevT.supLow : (v : Nat) → ((Σ k, LevT k) → LevT v) → LevT v
  | 0, _ => Tre.zero
  | w + 1, h => Tre.supL fun b => h (decLow w b)

/-- The argument space: suprema at every finite level. -/
abbrev TopT := Tre Empty (Σ k, LevT k)

/-- A level-`j` tree as a lumped index below level `w`. -/
def encodeLow : (w j : Nat) → j < w → LevT j → LowT w
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | w + 1, j, h, x =>
      if hj : j = w then .inr (hj ▸ x) else .inl (encodeLow w j (by omega) x)

/-- Level-`k` trees as arguments. -/
def toTop : (k : Nat) → LevT k → TopT
  | 0, t => Tre.embed (fun g => .supL g) (fun g => .supL g) t
  | w + 1, t => Tre.embed
      (fun g => .supH fun p => if h : p.1 < w then g (encodeLow w p.1 h p.2) else .zero)
      (fun g => .supH fun p => if h : p.1 = w then g (h ▸ p.2) else .zero) t

/-- **The collapsing functions**, by structural recursion on the argument. -/
def D : (v : Nat) → TopT → LevT v
  | v, .zero => LevT.Omega v
  | v, .succ t => LevT.epsNext v (D v t)
  | v, .lim f => LevT.lim v fun n => D v (f n)
  | v, .supL _ => LevT.zero v
  | v, .supH g =>
      let seq : (j : Nat) → Nat → LevT j := fun j n =>
        Nat.rec (motive := fun _ => LevT j) (LevT.Omega j) (fun _ acc => D j (g ⟨j, acc⟩)) n
      LevT.lim v fun m =>
        match m with
        | 0 => LevT.supLow v fun p => if p.1 < v then D v (g p) else LevT.zero v
        | i + 1 => LevT.lim v fun n => D v (g ⟨v + i, seq (v + i) n⟩)

/-- `Ω_ω` as an argument: the countable limit of the `Ω_k`. -/
def OmegaOmega : TopT := Tre.lim fun k => toTop k (LevT.Omega k)

/-- `n` further ε-numbers above `Ω_ω + 1`. -/
def epsIter : Nat → TopT → TopT
  | 0, x => x
  | n + 1, x => Tre.epsNext (epsIter n x)

/-- The countable tree `ψ₀(ε_{Ω_ω+n})` (heuristically). -/
def bigTree (n : Nat) : CTree := D 0 (epsIter (n + 1) (.succ OmegaOmega))

end BusyLean.Ordinal
