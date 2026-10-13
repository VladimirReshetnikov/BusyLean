import BusyLean.Contender6

/-!
# Contender 7: autonomous critical-point reflection

This file contains definitions only.  The comparison theorem and audits live in
`BusyLean/Comparison7.lean` and `test/Contender7Audit.lean`.

The existing Contender 6 reflects along `index`, the join of all `W Nat` trees
defined by the finite-level W-language.  Here we first regard that tree as the
base of a separate, transparent Brouwer-tree notation language.  We close the
base under ordinal-style addition, multiplication, exponentiation, derivatives
(first fixed points above a parameter), a finite critical-function hierarchy,
and then a diagonal/common-critical-point constructor.  Forty-two visible
branches expose successively stronger higher derivatives; branch zero is the
old `index`, which permits a direct comparison without any monotonicity claim.

All recursion is structural on `Nat`, `OTree`, or `WTree`.  In particular the
number is a closed computable `Nat`; it contains no `noncomputable`, `partial`,
`unsafe`, `opaque`, `extern`, choice oracle, or previous contender constant.
Do not evaluate `contender_7`.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

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

/-- Contender 6's self-generated index, imported only as structural seed data. -/
def contender7Base : Autonomous.OTree := Autonomous.encode index

/-- Branch zero is exactly the old index.  Branch `k+1` is the `k`-th higher
fixed-point closure of a successor of that seed. -/
def contender7Branch : Nat -> WTree Nat
  | 0 => index
  | k + 1 =>
      Autonomous.realize
        (Autonomous.hyper k (Autonomous.OTree.succ contender7Base))

/-- The new autonomous reflection schedule. -/
def contender7Index : WTree Nat := .node contender7Branch

/-- The new reflection family. -/
def contender7Family (n : Nat) : Nat := stage p5Family contender7Index n

/-- **Contender 7.** Never evaluate it. -/
def contender_7 : Nat := contender7Family 42

end BusyLean
