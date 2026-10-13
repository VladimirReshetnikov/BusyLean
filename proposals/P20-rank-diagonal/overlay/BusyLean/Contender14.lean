import BusyLean.Contender13
import BusyLean.Contender9
import BusyLean.Autonomous
import BusyLean.HyperReflection

/-!
# Contender 14: bi-diagonal rank reflection over dynamic-kind System Fω

Contender 13 performs one unary-oracle reflection over dynamic-kind System Fω.
The present construction strengthens all three axes at once.

1. `Fd.reflectFamily` gives that language a countable oracle family, encoded by
   `packFamily`, while retaining an explicit maximum over all visible family
   coordinates.
2. `rankLift` raises autonomous reflection through a finite hierarchy of
   meta-levels.  The rank at input `n` is `family13 n + 1` rather than a fixed
   numeral.
3. The W-tree schedule is also diagonal: the number of higher derivatives
   stacked above Contender 12's tree is `family13 n + 1`.

The ranked family is finally reflected once more by dynamic-kind System Fω.
Thus `F14 n` strictly exceeds both Contender 13's family at `n` and every
visible coordinate of the entire rank-diagonal family.

**Do not evaluate `contender_14`.**
-/

namespace BusyLean.Fd

/-- Dynamic-kind System Fω reflection with a countable oracle family.

The family is exposed to object-language programs through the computable code
`packFamily fs (2^i * (2*m+1)) = fs i m`.  The explicit prefix maximum is what
makes progressivity independent of any semantic monotonicity of programs.
-/
def reflectFamily (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN
    (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum
      (fvalue (BusyLean.packFamily fs) n) (ctmsUpTo n))

end BusyLean.Fd

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Contender 13's construction as a function of its input:
`family13 42 = contender_13`. -/
def family13 (n : Nat) : Nat := F13 (F13 n)

/-- The previous construction determines both the meta-rank and schedule rank. -/
def diagonalRank14 (n : Nat) : Nat := family13 n + 1

/-- A schedule obtained by stacking a previous-number-controlled number of
higher critical derivatives above Contender 12's already autonomous tree. -/
def schedule14 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (diagonalRank14 n) (Autonomous.encode tree12))

/-- One family-aware dynamic-kind reflection step, viewed as a transformer. -/
def fdFamilyTransformer : Transformer :=
  fun fs _ n => Fd.reflectFamily fs n

/-- The seed family repeats Contender 13's construction at every coordinate. -/
def seed13 : W.Family := fun _ => family13

/-- The rank-diagonal family at input `n`.

Both the meta-rank and the autonomous schedule are controlled by
`family13 n + 1`; neither is a fixed finite amplification.
-/
def rankFamily14 (n : Nat) : W.Family :=
  rankLift (schedule14 n) (diagonalRank14 n) fdFamilyTransformer seed13

/-- The final dynamic-kind reflection over the complete rank-diagonal family. -/
def F14 (n : Nat) : Nat := Fd.reflectFamily (rankFamily14 n) n

/-- **Contender 14.** Never evaluate it. -/
def contender_14 : Nat := F14 (F14 42)

end BusyLean
