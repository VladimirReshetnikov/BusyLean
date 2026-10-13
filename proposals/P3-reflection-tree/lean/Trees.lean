import Init

/-!
# Explicit structural trees for the big-number construction

No ordinal quotient or well-ordering axiom is used. `Stage` is an ordinary
strictly positive inductive type. Its infinitely branching nodes are given
by total functions. All definitions below use structural recursion.

The Veblen-inspired part is a recipe for trees, not a claim that arbitrary
trees are canonical ordinal notations. In particular, equivalent ordinal
presentations must not be silently identified.
-/

namespace Biggest

inductive Stage where
  | zero : Stage
  | succ : Stage → Stage
  | lim : (Nat → Stage) → Stage

def treeIter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (treeIter f n x)

def stageNat : Nat → Stage
  | 0 => .zero
  | n + 1 => .succ (stageNat n)

def stageOmega : Stage := .lim stageNat

def stageAdd (a : Stage) : Stage → Stage
  | .zero => a
  | .succ b => .succ (stageAdd a b)
  | .lim s => .lim (fun n => stageAdd a (s n))

def stageMul (a : Stage) : Stage → Stage
  | .zero => .zero
  | .succ b => stageAdd (stageMul a b) a
  | .lim s => .lim (fun n => stageMul a (s n))

def omegaPow : Stage → Stage
  | .zero => .succ .zero
  | .succ a => stageMul (omegaPow a) stageOmega
  | .lim s => .lim (fun n => omegaPow (s n))

def omegaClose (f : Stage → Stage) (x : Stage) : Stage :=
  .lim (fun n => treeIter f n x)

def enumerateClosure (close : Stage → Stage) : Stage → Stage
  | .zero => close .zero
  | .succ a => close (.succ (enumerateClosure close a))
  | .lim s => .lim (fun n => enumerateClosure close (s n))

def derivative (f : Stage → Stage) : Stage → Stage :=
  enumerateClosure (omegaClose f)

def closureRound (fs : Nat → Stage → Stage) : Nat → Stage → Stage
  | 0, x => x
  | n + 1, x => fs n (closureRound fs n x)

def closureOrbit (fs : Nat → Stage → Stage) (x : Stage) : Nat → Stage
  | 0 => x
  | n + 1 => closureRound fs (n + 1) (closureOrbit fs x n)

def commonClose (fs : Nat → Stage → Stage) (x : Stage) : Stage :=
  .lim (closureOrbit fs x)

def commonDerivative (fs : Nat → Stage → Stage) : Stage → Stage :=
  enumerateClosure (commonClose fs)

def veblenTree (base : Stage → Stage) : Stage → Stage → Stage
  | .zero => base
  | .succ a => derivative (veblenTree base a)
  | .lim s => commonDerivative (fun n => veblenTree base (s n))

def criticalLift (base : Stage → Stage) : Stage → Stage :=
  derivative (fun a => veblenTree base a .zero)

def gammaTree : Stage := criticalLift omegaPow .zero

/- The remaining construction amplifies at every finite functional type. -/

def TreeLevel : Nat → Type
  | 0 => Stage
  | n + 1 => TreeLevel n → TreeLevel n

def levelLimit : (n : Nat) → (Nat → TreeLevel n) → TreeLevel n
  | 0, s => .lim s
  | n + 1, s => fun x => levelLimit n (fun k => s k x)

def levelSucc : (n : Nat) → TreeLevel n → TreeLevel n
  | 0, x => .succ x
  | n + 1, f => fun x => levelSucc n (f x)

def omegaAmplifier (n : Nat) : TreeLevel (n + 2) :=
  fun f x => levelSucc n (levelLimit n (fun k => treeIter f k x))

def levelSeed (f : Stage → Stage) (a : Stage) : (n : Nat) → TreeLevel n
  | 0 => a
  | 1 => f
  | n + 2 => omegaAmplifier n

def descendLevel (f : Stage → Stage) (a : Stage) :
    (n : Nat) → TreeLevel n → Stage
  | 0, x => x
  | n + 1, g => descendLevel f a n (g (levelSeed f a n))

def higherTower (f : Stage → Stage) (a : Stage) : Stage :=
  .succ (.lim (fun n => descendLevel f a (n + 2) (omegaAmplifier n)))

/- Structural iteration indexed by a tree. It does not require assigning
   any ordinals to trees or proving an external relation well founded. -/

def stageIter (f : Stage → Stage) : Stage → Stage → Stage
  | .zero, x => x
  | .succ a, x => f (stageIter f a x)
  | .lim s, x => .lim (fun n => stageIter f (s n) x)

def promoteTreeFunction (f : Stage → Stage) (a : Stage) : Stage :=
  .succ (stageIter (higherTower f) (higherTower f a) a)

def startingTreeFunction (a : Stage) : Stage :=
  .succ (criticalLift omegaPow a)

def promotedTreeFunction (a : Stage) : Stage :=
  .succ (.lim (fun n => treeIter promoteTreeFunction (n + 1) startingTreeFunction a))

def finalStage : Stage :=
  let seed := promotedTreeFunction gammaTree
  .succ (stageIter promotedTreeFunction seed seed)

end Biggest
