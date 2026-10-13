import BusyLean.MetaReflection
import BusyLean.Autonomous
import BusyLean.Contender13

/-!
# Contender 14: self-height operator power over dynamic-kind System F-omega

Contender 13 performs one reflection over dynamic-kind System F-omega.  This
successor first turns that reflection into a progressive transformer on
countable oracle families, then applies the repository's whole operator-stage
construction repeatedly.

The fixed schedule `tree14` places another 42-level autonomous closure above
Contender 12's schedule.  At input `n`, the number of operator-stage rounds is
`family13 n + 1`, and the final transformer is evaluated at `family13 n`.
Thus the previous construction controls both the seed and the height of a
qualitatively stronger construction, without mentioning the constant for
Contender 13.

All definitions are structural and executable.  Do not evaluate
`contender_14`.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Dynamic-kind reflection lifted from one unary oracle to a countable oracle
family.  The packed oracle is seen by object-language programs; the prefix
maximum makes every visible family coordinate an explicit lower bound. -/
def reflect14 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 +
    BigNumber.maxN
      (W.prefixMax (fun i => fs i n) n)
      (Fd.reflectFd (packFamily fs) n)

/-- One family-aware dynamic-kind reflection step, as a transformer. -/
def fdTransformer : Transformer := fun fs _ n => reflect14 fs n

/-- A schedule strictly more elaborate than Contender 12's schedule: another
42-level autonomous closure is stacked above `tree12`.  This is syntax for a
well-founded tree, not a claim about quotient-level ordinal identities. -/
def tree14 : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper 42 (Autonomous.encode tree12))

/-- Iterate the complete operator-stage construction along a fixed schedule.
Each successor level treats the preceding transformer as its new base step. -/
def operatorPower (tree : WTree Nat) (base : Transformer) :
    Nat → Transformer
  | 0 => base
  | k + 1 => operatorStage (operatorPower tree base k) tree

/-- Contender 13's construction as a function of its input.  In particular,
`family13 42` is definitionally the previous contender, but that constant is
not used here. -/
def family13 (n : Nat) : Nat := F13 (F13 n)

/-- The self-height dynamic-kind operator power.

At input `n`, perform `family13 n + 1` complete operator stages, seed every
oracle coordinate with `family13`, and evaluate at the previous-family value
`family13 n`. -/
def F14 (n : Nat) : Nat :=
  operatorPower tree14 fdTransformer (family13 n + 1)
    (fun _ => family13) (family13 n) (family13 n)

/-- **Contender 14.** Never evaluate it. -/
def contender_14 : Nat := F14 (F14 42)

end BusyLean
