import BusyLean.Contender13
import BusyLean.MetaReflection
import BusyLean.Autonomous

/-!
# Namespaced reconstruction of the incoming diagonal operator tower

This is the mathematical definition from
`BusyLean_Contender14_DiagonalOperatorTower.zip`, placed in a private namespace
so that it can coexist with the other incoming Contender-14 proposals.
-/

namespace BusyLean.Incoming14.DiagonalOperatorTower

open BigNumber (WTree)

/-- Dynamic-kind System F-omega reflection with a countable oracle family. -/
def reflect14 (fs : BusyLean.W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN
    (BusyLean.W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum
      (BusyLean.Fd.fvalue (BusyLean.packFamily fs) n)
      (BusyLean.Fd.ctmsUpTo n))

/-- One family-aware dynamic-kind reflection step. -/
def fdFamilyTransformer : BusyLean.Transformer :=
  fun fs _ n => reflect14 fs n

/-- Rank-dependent schedule with a canonical leaf and unbounded derivatives. -/
def schedule14 (k : Nat) : WTree Nat :=
  .node (fun j =>
    match j with
    | 0 => .leaf
    | r + 1 =>
        BusyLean.Autonomous.realize
          (BusyLean.Autonomous.hyper (k + r + 1)
            (BusyLean.Autonomous.encode BusyLean.tree12)))

/-- Iterate complete operator stages through a rank-dependent schedule. -/
def diagonalOperatorTower (schedule : Nat → WTree Nat)
    (base : BusyLean.Transformer) : Nat → BusyLean.Transformer
  | 0 => base
  | k + 1 =>
      BusyLean.operatorStage
        (diagonalOperatorTower schedule base k) (schedule k)

/-- Contender 13 as a family. -/
def family13 (n : Nat) : Nat := BusyLean.F13 (BusyLean.F13 n)

/-- The self-indexed tower. -/
def tower14 (n : Nat) : BusyLean.Transformer :=
  diagonalOperatorTower schedule14 fdFamilyTransformer (family13 n)

/-- Pointwise candidate family. -/
def F14 (n : Nat) : Nat := tower14 n (fun _ => family13) n n

/-- Closed incoming candidate. -/
def contender_14 : Nat := F14 (F14 42)

end BusyLean.Incoming14.DiagonalOperatorTower
