import BusyLean.HyperReflection
import BusyLean.Autonomous
import BusyLean.Contender13

/-!
# Contender 14: diagonal hyperreflection over dynamic-kind System F-omega

Contender 13 supplies the strongest object language in the repository, but it
uses that language for one ordinary reflection step.  Contender 14 first turns
dynamic-kind reflection into a progressive transformer on countable oracle
families, then applies a diagonal hierarchy of transformer lifts.

For input `n`:

* `family13 n = F13 (F13 n)` is Contender 13's construction as a family;
* `schedule14 n` stacks `family13 n + 42` explicit higher derivatives above
  Contender 12's operator schedule;
* `rank14 n = family13 n + 1` is the diagonal hyperreflection rank;
* `F14 n` applies that rank to dynamic-kind family reflection and seeds it
  with the whole family `family13`.

The definition never mentions the constant `contender_13`.  All recursion is
structural, and the resulting natural number is computable in principle.

**Do not evaluate `contender_14`.**
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Dynamic-kind System F-omega reflection with a countable oracle family.
The packed unary oracle is available to programs, while the visible prefix
maximum makes the resulting transformer progressive without any monotonicity
assumption. -/
def reflectFdFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fd.fvalue (packFamily fs) n) (Fd.ctmsUpTo n))

/-- Family reflection packaged as a transformer.  The output coordinate is
irrelevant; every coordinate receives the same reflected value. -/
def fdFamilyTransformer : Transformer :=
  fun fs _ n => reflectFdFamily fs n

/-- Contender 13's construction as a function of its input:
`family13 42 = contender_13`. -/
def family13 (n : Nat) : Nat := F13 (F13 n)

/-- The input-dependent autonomous schedule.  The construction is transparent
syntax for a well-founded tree; no quotient-level ordinal identity is used. -/
def schedule14 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family13 n + 42) (Autonomous.encode tree12))

/-- The diagonal rank, already larger than Contender 13's family value at the
same input. -/
def rank14 (n : Nat) : Nat := family13 n + 1

/-- The diagonal hyperreflection family. -/
def F14 (n : Nat) : Nat :=
  diagonalLift (schedule14 n) (rank14 n) fdFamilyTransformer
    (fun _ => family13) n n

/-- **Contender 14.** Never evaluate it. -/
def contender_14 : Nat := F14 (F14 42)

end BusyLean
