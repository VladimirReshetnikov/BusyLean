import BusyLean.Contender53

/-!
# Tree-indexed large elimination

The earlier tree readers recurse over a run-time tree into a type fixed by the
program text.  This file introduces a different resource: the tree itself
computes the semantic result type.

For a countable tree `a`, `LargeTy a` is

* `Nat` at zero;
* the endomorphism space on `LargeTy b` at `succ b`;
* the dependent product `forall i, LargeTy (f i)` at `lim f`.

Thus one closed Lean definition traverses types of unbounded finite order and,
at limits, non-uniform dependent products whose fibers are selected by the
run-time tree.  This is a small, transparent large-elimination kernel rather
than another wrapper around the previous reflection operator.
-/

namespace BusyLean

open Ordinal (CTree)

/-- The semantic type computed by a countable tree.

This is the new large-elimination step: recursion on a value in `CTree`
produces a value in `Type`, and the recursive occurrences appear inside the
result type itself.  The unreachable higher-supremum constructors of `CTree`
are given the conservative interpretation `Nat`.
-/
def LargeTy : CTree → Type
  | .zero => Nat
  | .succ a => LargeTy a → LargeTy a
  | .lim f => (i : Nat) → LargeTy (f i)
  | .supL _ => Nat
  | .supH _ => Nat

/-- The canonical endomorphism at the type computed by `a`.

At zero it is the numeric base `g`.  At a successor it performs `n`-fold
iteration of an endomorphism.  At a limit it acts pointwise, but at different
fiber types `LargeTy (f i)`.
-/
def largeStep (g : Nat → Nat) : (a : CTree) → Nat → LargeTy a → LargeTy a
  | .zero, _, x => g x
  | .succ _, n, h => Ordinal.iterN h n
  | .lim f, n, x => fun i => largeStep g (f i) n (x i)
  | .supL _, _, x => g x
  | .supH _, _, x => g x

/-- A canonical inhabitant of every tree-computed semantic type. -/
def largeSeed (g : Nat → Nat) (n : Nat) : (a : CTree) → LargeTy a
  | .zero => n
  | .succ a => largeStep g a n
  | .lim f => fun i => largeSeed g n (f i)
  | .supL _ => n
  | .supH _ => n

/-- Collapse a value at a tree-computed type back to a natural number.

At a successor, apply the higher-type value to the canonical inhabitant of its
argument type.  At a limit, observe the first `n+1` fibers and take their
maximum.  Hence every evaluation is finite and executable in principle.
-/
def largeCollapse (g : Nat → Nat) (n : Nat) : (a : CTree) → LargeTy a → Nat
  | .zero, x => x
  | .succ a, F => largeCollapse g n a (F (largeSeed g n a))
  | .lim f, X =>
      Ordinal.maxUpTo (fun i => largeCollapse g n (f i) (X i)) n
  | .supL _, x => x
  | .supH _, x => x

/-- Evaluate the canonical inhabitant at the type computed by `a`, then
collapse it to a natural number. -/
def largeElim (g : Nat → Nat) (a : CTree) (n : Nat) : Nat :=
  largeCollapse g n a (largeSeed g n a)

/-- Add two semantic-order levels.  Repeating this operation makes the
higher-type order itself a run-time parameter. -/
def ramify (a : CTree) : Nat → CTree
  | 0 => a
  | k + 1 => .succ (.succ (ramify a k))

@[simp] theorem largeElim_zero (g : Nat → Nat) (n : Nat) :
    largeElim g .zero n = n := rfl

@[simp] theorem largeElim_one (g : Nat → Nat) (n : Nat) :
    largeElim g (.succ .zero) n = g n := rfl

/-- At semantic order two, large elimination is already diagonal iteration of
`g`: apply the `n`-fold iterator to `g`, then to `n`. -/
@[simp] theorem largeElim_two (g : Nat → Nat) (n : Nat) :
    largeElim g (.succ (.succ .zero)) n = Ordinal.iterN g n n := rfl

@[simp] theorem largeElim_lim (g : Nat → Nat) (f : Nat → CTree) (n : Nat) :
    largeElim g (.lim f) n =
      Ordinal.maxUpTo (fun i => largeElim g (f i) n) n := rfl

@[simp] theorem ramify_zero (a : CTree) : ramify a 0 = a := rfl

@[simp] theorem ramify_succ (a : CTree) (k : Nat) :
    ramify a (k + 1) = .succ (.succ (ramify a k)) := rfl

end BusyLean
