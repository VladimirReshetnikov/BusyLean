import BusyLean.Contender10

/-!
# Contender 11: forest reflection of kind-polymorphic System Fω

This lifts Contender 10's kind-polymorphic reflection from a unary oracle to
a dynamically indexed oracle family and iterates it along the W-language's
self-indexed tree `index`.
-/

namespace BusyLean

/-- One reflection step over kind-polymorphic System Fω with an oracle family. -/
def reflect11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))

/-- Forest reflection of kind-polymorphic System Fω along a W-tree. -/
def stage11 (seed : W.Family) : BigNumber.WTree Nat → Nat → Nat
  | .leaf => reflect11 seed
  | .node g => reflect11 (fun i => stage11 seed (g i))

/-- Contender 10's construction as a function of its input. -/
def family10 (n : Nat) : Nat := F10 (F10 n)

/-- The oracle family visible at the root of `index`. -/
def rootFamily11 : W.Family :=
  fun i => stage11 (fun _ => family10) (treesOfDepth i)

/-- Kind-polymorphic forest reflection along the W-language's self-index. -/
def F11 (n : Nat) : Nat := stage11 (fun _ => family10) index n

/-- **Contender 11.** Never evaluate it. -/
def contender_11 : Nat := F11 (F11 42)

end BusyLean
