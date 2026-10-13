import BusyLean.Contender13
import BusyLean.MetaReflection
import BusyLean.Autonomous

/-!
# Namespaced reconstruction of ramified dynamic operator reflection

This is the mathematical definition from `BusyLean_Contender14_RDOR.zip`,
placed in a private namespace so that all current incoming candidates can be
bounded simultaneously.
-/

namespace BusyLean.Incoming14.RDOR

open BigNumber (WTree)

/-- Dynamic-kind reflection with a packed countable oracle family. -/
def reflectFdFamily (fs : BusyLean.W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN
    (BusyLean.W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum
      (BusyLean.Fd.fvalue (BusyLean.packFamily fs) n)
      (BusyLean.Fd.ctmsUpTo n))

/-- One family-aware reflection step. -/
def fdFamilyTransformer : BusyLean.Transformer :=
  fun fs _ n => reflectFdFamily fs n

/-- A second autonomous schedule above Contender 12. -/
def tree14 : WTree Nat :=
  BusyLean.Autonomous.realize
    (BusyLean.Autonomous.hyper 42
      (BusyLean.Autonomous.encode BusyLean.tree12))

/-- Feed a transformer's output back through a complete operator stage. -/
def towerStep (base : BusyLean.Transformer) : BusyLean.Transformer :=
  fun seed => (BusyLean.operatorStage base tree14) (base seed)

/-- Ramified operator tower. -/
def operatorTower : Nat → BusyLean.Transformer
  | 0 => fdFamilyTransformer
  | k + 1 => towerStep (operatorTower k)

/-- Contender 13 as a family. -/
def family13 (n : Nat) : Nat := BusyLean.F13 (BusyLean.F13 n)

/-- Finite right-associated iteration of `F13`. -/
def iterateF13 : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => BusyLean.F13 (iterateF13 k n)

/-- Seed exposing all finite additional `F13` iterates by coordinate. -/
def seed13 : BusyLean.W.Family :=
  fun i n => iterateF13 i (family13 n)

/-- Pointwise candidate family. -/
def F14 (n : Nat) : Nat :=
  operatorTower (n + 1) seed13 n n

/-- Closed incoming candidate. -/
def contender_14 : Nat := F14 (F14 42)

end BusyLean.Incoming14.RDOR
