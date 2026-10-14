/-!
# Brouwer trees and the Hardy hierarchy (rung 3's base)

Ordinals are written as Brouwer trees (countably branching well-founded trees):
`zero`, `succ a`, and `lim f` for a fundamental sequence `f : ℕ → BTree`.
Addition, multiplication by a number and `ω`-exponentiation are defined by
recursion on the trees, `ω_{k+1} = ω^{ω_k}`, and `ε₀ = lim ω_k`.

The hierarchy is Hardy's: `H_0(y) = y`, `H_{a+1}(y) = H_a(y + 1)`, and at a
limit, `H_{lim f}(y)` is the largest of `H_{f 0}(y), …, H_{f y}(y)`. Taking the
maximum over the first `y + 1` terms of the fundamental sequence (instead of
only the `y`-th term) makes every `H_a` monotone without any condition on the
tree; it is a standard robust variant of the Hardy hierarchy.

This file imports nothing. Rung 3 (`Bachmann.lean`) builds on it; `ε₀` and
`Feps` serve as the bound in the ordinal analysis of System T.
-/

namespace BusyLean.Indep.Eps

/-- Brouwer trees: countable ordinals given with fundamental sequences. -/
inductive BTree where
  | zero : BTree
  | succ : BTree → BTree
  | lim : (Nat → BTree) → BTree

namespace BTree

/-- `a + b`, by recursion on `b`. -/
def add (a : BTree) : BTree → BTree
  | zero => a
  | succ b => succ (add a b)
  | lim f => lim fun i => add a (f i)

/-- `a · i` for a number `i`. -/
def mulNat (a : BTree) : Nat → BTree
  | 0 => zero
  | i + 1 => add (mulNat a i) a

/-- `ω^a`: `ω^0 = 1`, `ω^{a+1} = lim_i ω^a · i`, `ω^{lim f} = lim_i ω^{f i}`. -/
def opow : BTree → BTree
  | zero => succ zero
  | succ a => lim fun i => mulNat (opow a) i
  | lim f => lim fun i => opow (f i)

/-- `ω`. -/
def omega : BTree := lim fun i => mulNat (succ zero) i

/-- The towers `ω_0 = ω`, `ω_{k+1} = ω^{ω_k}`. -/
def tower : Nat → BTree
  | 0 => omega
  | k + 1 => opow (tower k)

/-- `ε₀ = lim_k ω_k`. -/
def epsilon0 : BTree := lim tower

end BTree

/-- The largest of `g 0, …, g y`. -/
def maxUpTo (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | y + 1 => max (maxUpTo g y) (g (y + 1))

/-- The Hardy hierarchy along Brouwer trees (limits take the maximum over the
first `y + 1` terms of the fundamental sequence). -/
def hardy : BTree → Nat → Nat
  | .zero, y => y
  | .succ a, y => hardy a (y + 1)
  | .lim f, y => maxUpTo (fun i => hardy (f i) y) y

end BusyLean.Indep.Eps

namespace BusyLean.Indep

/-- The Hardy hierarchy at `ε₀`. -/
def Feps (n : Nat) : Nat := Eps.hardy Eps.BTree.epsilon0 n

end BusyLean.Indep
