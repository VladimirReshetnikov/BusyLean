import Init

/-!
# Constructive Brouwer trees and iterated functional diagonals

All recursions in this file are structural.  `BTree` is a type of raw
well-founded trees, not a quotient or a canonical ordinal notation system.
In particular, no equality of ordinal ranks is used in the number comparison.
-/

inductive BTree : Type where
  | zero : BTree
  | succ : BTree → BTree
  | lim : (Nat → BTree) → BTree

namespace BTree

def fold {α : Type} (z : α) (s : α → α) (l : (Nat → α) → α) : BTree → α
  | .zero => z
  | .succ a => s (fold z s l a)
  | .lim f => l (fun n => fold z s l (f n))

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterate f n (f x)

def finite (n : Nat) : BTree := iterate .succ n .zero

def omega : BTree := .lim finite

def add (a : BTree) : BTree → BTree := fold a .succ .lim

def mul (a : BTree) : BTree → BTree :=
  fold .zero (fun r => add r a) .lim

def power (a : BTree) : BTree → BTree :=
  fold (.succ .zero) (fun r => mul r a) .lim

def omegaPow : BTree → BTree := power omega

/-- Iterate a tree operation from the successor of the starting tree. -/
def closure (f : BTree → BTree) (a : BTree) : BTree :=
  .lim (fun n => iterate f n (.succ a))

/-- The structural fixed-point enumeration schedule associated to `f`. -/
def derivative (f : BTree → BTree) : BTree → BTree :=
  fold (closure f .zero) (closure f) .lim

/-- A common fixed-point schedule for a countable family of operations. -/
def common (fs : Nat → BTree → BTree) : BTree → BTree :=
  derivative (fun a => .lim (fun n => fs n a))

/-- A raw-tree Veblen-style schedule, with the initial operation parameterized. -/
def veblenFrom (f : BTree → BTree) : BTree → BTree → BTree :=
  fold f derivative common

def veblenBase : BTree → BTree → BTree := veblenFrom omegaPow

def veblenDiagonal : BTree → BTree :=
  derivative (fun a => veblenBase a .zero)

/-
`Stage 0` consists of tree functions.  Every next stage consists of
endomorphisms of the preceding stage.  Pointwise limits and diagonals lift
uniformly through this entire finite-type tower.  The type family itself uses
dependent natural-number recursion; there is no fixed bound on its height.
-/
def Stage : Nat → Type
  | 0 => BTree → BTree
  | n + 1 => Stage n → Stage n

def stageLimit : (k : Nat) → (Nat → Stage k) → Stage k
  | 0, fs => common fs
  | k + 1, fs => fun x => stageLimit k (fun n => fs n x)

def stageDiagonal : (k : Nat) → (BTree → Stage k) → Stage k
  | 0, fs => derivative (fun a => fs a .zero)
  | k + 1, fs => fun x => stageDiagonal k (fun a => fs a x)

/-- Reflect tree-indexed iteration through one finite-type level. -/
def liftStage (k : Nat) : Stage (k + 2) :=
  fun step seed => stageDiagonal k (fun a => fold seed step (stageLimit k) a)

def levelSeed : (k : Nat) → Stage k
  | 0 => omegaPow
  | 1 => derivative
  | k + 2 => liftStage k

/-- Apply every higher functional to the canonical seed one level below. -/
def collapse : (k : Nat) → Stage k → BTree → BTree
  | 0, f => f
  | k + 1, f => collapse k (f (levelSeed k))

theorem collapse_one : collapse 1 (levelSeed 1) = derivative omegaPow := rfl

theorem collapse_two : collapse 2 (levelSeed 2) = veblenDiagonal := rfl

/-- Diagonalize simultaneously over all finite functional levels. -/
def universeStep (a : BTree) : BTree :=
  .lim (fun k => collapse (k + 2) (levelSeed (k + 2)) (.succ a))

/-- A closed, structurally generated schedule for the flagship number. -/
def index : BTree := .lim (fun n => iterate universeStep (n + 1) .zero)

/-- The numerical hierarchy driven by any strictly inflationary base. -/
def fast (base : Nat → Nat) : BTree → Nat → Nat :=
  fold base (fun f n => iterate f (n + 2) n) (fun fs n => fs n n)

theorem iterate_ge (f : Nat → Nat) (hf : ∀ x, x < f x) (k x : Nat) :
    x ≤ iterate f k x := by
  induction k generalizing x with
  | zero => exact Nat.le_refl x
  | succ k ih =>
    exact Nat.le_trans (Nat.le_of_lt (hf x)) (ih (f x))

theorem iterate_gt (f : Nat → Nat) (hf : ∀ x, x < f x) (k x : Nat) :
    x < iterate f (k + 1) x :=
  Nat.lt_of_lt_of_le (hf x) (iterate_ge f hf k (f x))

theorem fast_inflationary (base : Nat → Nat) (hb : ∀ x, x < base x)
    (a : BTree) (n : Nat) : n < fast base a n := by
  induction a generalizing n with
  | zero => exact hb n
  | succ a ih => exact iterate_gt (fast base a) ih (n + 1) n
  | lim f ih => exact ih n n

theorem fast_base_le (base : Nat → Nat) (hb : ∀ x, x < base x)
    (a : BTree) (n : Nat) : base n ≤ fast base a n := by
  induction a generalizing n with
  | zero => exact Nat.le_refl (base n)
  | succ a ih =>
    exact Nat.le_trans (ih n)
      (iterate_ge (fast base a) (fast_inflationary base hb a)
        (n + 1) (fast base a n))
  | lim f ih => exact ih n n

theorem fast_succ_gt (base : Nat → Nat) (hb : ∀ x, x < base x)
    (a : BTree) (n : Nat) : fast base a n < fast base (.succ a) n :=
  iterate_gt (fast base a) (fast_inflationary base hb a) n (fast base a n)

end BTree

def treeIndex : BTree := BTree.index

#print axioms treeIndex
#print axioms BTree.fast_inflationary
#print axioms BTree.fast_base_le
#print axioms BTree.fast_succ_gt
