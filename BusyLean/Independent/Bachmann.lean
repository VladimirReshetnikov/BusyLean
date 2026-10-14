import BusyLean.Independent.EpsilonHardy

/-!
# Independent tower, rung 3: the Hardy hierarchy along a collapsed tree

This rung is an **ordinal-notation hierarchy** with a collapsing function.
Countable ordinals are Brouwer trees (`BTree`, in `EpsilonHardy.lean`, which
also defines `ω^·` and the Hardy hierarchy). Above them sit **`Ω`-trees**
(`OTree`): besides countable limits they have limits `sup f` over *all*
Brouwer trees, `f : BTree → OTree`, so `Ω = sup (embedding of BTree)` is the
first uncountable. On `Ω`-trees, `+`, `·b` and `Ω^·` are defined by recursion,
and `ε_{Ω+1} = lim (Ω, Ω^Ω, Ω^{Ω^Ω}, …)`.

The collapse is Bachmann's, written as a fold over the `Ω`-tree:

* `φ_0(b) = ω^b`,
* `φ_{a+1}(b) = lim (b + 1, φ_a(b + 1), φ_a(φ_a(b + 1)), …)`, the next fixed
  point of `φ_a` after `b`,
* `φ_{lim f}(b) = lim_m φ_{f m}(b)`,
* `φ_{sup f}(b) = φ_{f b}(b)`: at an `Ω`-limit the current argument `b` itself
  picks the branch.

`θ = φ_{ε_{Ω+1}}(0)` is a tree for the Bachmann–Howard ordinal, and
`F3 n = H_θ(n)`.

**Do not evaluate `contender_3`.**
-/

namespace BusyLean.Indep.Eps

/-- `Ω`-trees: countable limits and limits over all Brouwer trees. -/
inductive OTree where
  | zero : OTree
  | succ : OTree → OTree
  | lim : (Nat → OTree) → OTree
  | sup : (BTree → OTree) → OTree

namespace OTree

/-- Brouwer trees as `Ω`-trees. -/
def lift : BTree → OTree
  | .zero => zero
  | .succ a => succ (lift a)
  | .lim f => lim fun i => lift (f i)

/-- `Ω`, the limit of all Brouwer trees. -/
def Omega : OTree := sup lift

/-- `a + b`, by recursion on `b`. -/
def add (a : OTree) : OTree → OTree
  | zero => a
  | succ b => succ (add a b)
  | lim f => lim fun i => add a (f i)
  | sup f => sup fun x => add a (f x)

/-- `a · b` for a Brouwer tree `b`. -/
def mulB (a : OTree) : BTree → OTree
  | .zero => zero
  | .succ b => add (mulB a b) a
  | .lim f => lim fun i => mulB a (f i)

/-- `Ω^a`: `Ω^0 = 1`, `Ω^{a+1} = sup_b Ω^a · b`, limits pointwise. -/
def opow : OTree → OTree
  | zero => succ zero
  | succ a => sup fun b => mulB (opow a) b
  | lim f => lim fun i => opow (f i)
  | sup f => sup fun x => opow (f x)

/-- `Ω_0 = Ω`, `Ω_{k+1} = Ω^{Ω_k}`. -/
def tower : Nat → OTree
  | 0 => Omega
  | k + 1 => opow (tower k)

/-- `ε_{Ω+1} = lim_k Ω_k`. -/
def epsilon : OTree := lim tower

end OTree

/-- `g` iterated `m` times. -/
def iter (g : BTree → BTree) : Nat → BTree → BTree
  | 0, b => b
  | m + 1, b => g (iter g m b)

/-- Bachmann's collapse: `φ_a(b)` for an `Ω`-tree `a` and a Brouwer tree `b`. -/
def phi : OTree → BTree → BTree
  | .zero, b => BTree.opow b
  | .succ a, b => .lim fun m => iter (phi a) m (.succ b)
  | .lim f, b => .lim fun m => phi (f m) b
  | .sup f, b => phi (f b) b

/-- `θ = φ_{ε_{Ω+1}}(0)`, the Bachmann–Howard ordinal as a Brouwer tree. -/
def theta : BTree := phi OTree.epsilon .zero

end BusyLean.Indep.Eps

namespace BusyLean.Indep

/-- The Hardy hierarchy at the Bachmann–Howard tree. -/
def F3 (n : Nat) : Nat := Eps.hardy Eps.theta n

/-- **The ordinal rung**: `H_θ(H_θ(42))`. Never evaluate it. -/
def contender_3 : Nat := F3 (F3 42)

end BusyLean.Indep
