import BigNumber.Definitions

/-!
# Explicit ordinal notations above a tree

Adopted from proposal P7 ("critical-point reflection",
proposals/P7-critical-point-reflection), from the `Autonomous` namespace of its
`Contender7.lean`, unchanged. A transparent language of countably branching
trees with ordinal-style addition, multiplication, ω-powers, derivatives, a
finite critical hierarchy, a Γ-like common critical closure, and higher
derivatives. `encode` and `realize` convert to and from the W-language's
`W ℕ` trees, so the notations can be stacked *above* a language-defined index.
No ordinal identities are claimed: these are syntax for trees.
-/

namespace BusyLean

open BigNumber (WTree)

namespace Autonomous

/-- A transparent language of countably branching well-founded trees.  We use
it as syntax, not as a quotient by ordinal equality. -/
inductive OTree : Type where
  | zero : OTree
  | succ : OTree -> OTree
  | limit : (Nat -> OTree) -> OTree

/-- Finite iteration, exposed as a structural definition. -/
def iterate {A : Type u} (f : A -> A) : Nat -> A -> A
  | 0, x => x
  | k + 1, x => iterate f k (f x)

/-- Syntactic ordinal addition: replace each zero leaf of the second argument
by the first argument. -/
def add (a : OTree) : OTree -> OTree
  | .zero => a
  | .succ b => .succ (add a b)
  | .limit f => .limit (fun n => add a (f n))

/-- Syntactic ordinal multiplication, recursive in the right argument. -/
def mul (a : OTree) : OTree -> OTree
  | .zero => .zero
  | .succ b => add (mul a b) a
  | .limit f => .limit (fun n => mul a (f n))

/-- Syntactic ordinal exponentiation, recursive in the exponent. -/
def pow (a : OTree) : OTree -> OTree
  | .zero => .succ .zero
  | .succ b => mul (pow a b) a
  | .limit f => .limit (fun n => pow a (f n))

/-- The finite ordinal `n`. -/
def ofNat : Nat -> OTree
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

/-- A canonical omega-shaped tree. -/
def omega : OTree := .limit ofNat

/-- The normal-function syntax `a |-> omega^a`. -/
def omegaPow (a : OTree) : OTree := pow omega a

/-- Starting above `a`, iterate `f` and take the countable limit.  When `f`
represents a normal ordinal function this is its first fixed point above `a`.
The Lean construction itself needs no semantic normality assumption. -/
def derivative (f : OTree -> OTree) (a : OTree) : OTree :=
  .limit (fun n => iterate f (n + 1) (.succ a))

/-- Finite critical-function hierarchy.  Level zero is exponentiation by omega;
each successor level enumerates fixed points of the preceding level. -/
def critical : Nat -> OTree -> OTree
  | 0, a => omegaPow a
  | k + 1, a => derivative (fun b => critical k b) a

/-- A diagonal common-critical-point closure over every finite critical level.
It is Gamma-like, but the source deliberately makes no quotient-level ordinal
identity claim. -/
def autonomous (a : OTree) : OTree :=
  .limit (fun k => critical (k + 1) (.succ a))

/-- Higher derivatives of the autonomous closure. -/
def hyper : Nat -> OTree -> OTree
  | 0, a => autonomous a
  | k + 1, a => derivative (fun b => hyper k b) a

/-- Read an existing `W Nat` tree as an autonomous notation. -/
def encode : WTree Nat -> OTree
  | .leaf => .zero
  | .node f => .limit (fun n => encode (f n))

/-- Realize an autonomous notation as a `W Nat` schedule for forest reflection. -/
def realize : OTree -> WTree Nat
  | .zero => .leaf
  | .succ a =>
      .node (fun n =>
        match n with
        | 0 => realize a
        | _ + 1 => .leaf)
  | .limit f => .node (fun n => realize (f n))

end Autonomous

end BusyLean
