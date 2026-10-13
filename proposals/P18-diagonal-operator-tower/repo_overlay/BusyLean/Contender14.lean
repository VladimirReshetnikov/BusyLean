import BusyLean.Contender13
import BusyLean.MetaReflection
import BusyLean.Autonomous

/-!
# Contender 14: self-indexed diagonal operator reflection

The reflected object language is Contender 13's dynamic-kind System F-omega,
but the unary oracle is now a packed countable family.  A separate prefix
maximum makes the resulting transformer progressive without assuming the
(false) monotonicity of reflection in its oracle.

The base transformer is then lifted through a diagonal tower of operator
stages.  At rank `k`, `schedule14 k` has a canonical leaf branch (used by the
strict comparison proofs) and countably many branches carrying successively
higher autonomous schedules above Contender 12's `tree12`.

The tower height at input `n` is `family13 n = F13 (F13 n)`.  In particular,
the height at input 42 is definitionally Contender 13, but the definition never
mentions the constant `contender_13` itself.

```
family13 n  = F13 (F13 n)
tower14 n   = diagonalOperatorTower schedule14 fdFamilyTransformer (family13 n)
F14 n       = tower14 n (fun _ => family13) n n
contender_14 = F14 (F14 42)
```

All definitions are transparent, structural, and executable.  Do not evaluate
`contender_14`.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Dynamic-kind System F-omega reflection with a countable oracle family.

The family is presented to the object language through `packFamily`.  The
explicit prefix maximum is logically separate: it ensures that every visible
seed coordinate `fs i n`, for `i <= n`, is below the reflector even though
object-language evaluation is not monotone in the oracle. -/
def reflect14 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fd.fvalue (packFamily fs) n) (Fd.ctmsUpTo n))

/-- One family-aware dynamic-kind reflection step, packaged as a transformer.
The output coordinate is ignored, exactly as for the earlier primitive
reflection transformers. -/
def fdFamilyTransformer : Transformer := fun fs _ n => reflect14 fs n

/-- A rank-dependent autonomous schedule.

Branch zero is a leaf, giving a canonical embedded copy of one autonomous lift.
Branch `r+1` carries the `(k+r+1)`-st higher autonomous derivative above
Contender 12's schedule.  Thus every rank exposes an unbounded diagonal family
of schedules while retaining an explicit branch for direct inequalities. -/
def schedule14 (k : Nat) : WTree Nat :=
  .node (fun j =>
    match j with
    | 0 => .leaf
    | r + 1 =>
        Autonomous.realize
          (Autonomous.hyper (k + r + 1) (Autonomous.encode tree12)))

/-- Iterate operator-stage closure along a rank-dependent schedule.

At successor rank, the entire transformer from the previous rank becomes the
base transformer for a fresh operator stage. -/
def diagonalOperatorTower (schedule : Nat → WTree Nat)
    (base : Transformer) : Nat → Transformer
  | 0 => base
  | k + 1 =>
      operatorStage (diagonalOperatorTower schedule base k) (schedule k)

/-- Contender 13's construction as a function of its input.
Definitionally, `family13 42 = contender_13`. -/
def family13 (n : Nat) : Nat := F13 (F13 n)

/-- The self-indexed tower: its rank at input `n` is `family13 n`. -/
def tower14 (n : Nat) : Transformer :=
  diagonalOperatorTower schedule14 fdFamilyTransformer (family13 n)

/-- The diagonal operator tower, seeded by Contender 13's family. -/
def F14 (n : Nat) : Nat := tower14 n (fun _ => family13) n n

/-- **Contender 14.** Never evaluate it. -/
def contender_14 : Nat := F14 (F14 42)

end BusyLean
