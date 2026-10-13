import BusyLean.Ordinal.TreeUniverses2

/-!
# Higher-order universe operators

`TreeUniverses2` builds universes with two operations, `next` and `union`.
Here universe-building operators are themselves iterated. For an operator
`F : Univ → Univ`, the universe `Φ F U` is the union of `F`'s finite iterates
from `U`, the closure point of `F` above `U`. So:

* `Φ next` jumps to the next universe closed under `next` (inaccessible-like);
* `Φ (Φ next)` jumps to the next limit of those, and so on.

Operators are indexed by tree ordinals by structural recursion:
`ΦT 0 = next`, `ΦT (a+1) = Φ (ΦT a)`, `ΦT (lim f) U = union (ΦT (f i) U)`.
Each round collapses inside the universe after `ΦT Λ base`, where `Λ` is the
previous round's tree. The rounds climb a hierarchy of inaccessible-like
closures.
-/

namespace BusyLean.Ordinal

namespace U2

/-- Finite iterates of a universe operator. -/
def iterU (F : Univ → Univ) (U : Univ) : Nat → Univ
  | 0 => U
  | k + 1 => F (iterU F U k)

/-- The closure point of `F` above `U`. -/
def Φ (F : Univ → Univ) (U : Univ) : Univ := Univ.union (iterU F U)

/-- Universe operators indexed by tree ordinals. -/
def ΦT : CTree → Univ → Univ
  | .zero => Univ.next
  | .succ a => Φ (ΦT a)
  | .lim f => fun U => Univ.union fun i => ΦT (f i) U
  | .supL _ => Univ.next
  | .supH _ => Univ.next

/-- One round: collapse in the universe after `ΦT Λ base`. -/
def opRound (Λ : CTree) : CTree := universeTree (ΦT Λ Univ.base)

/-- `k` rounds above Contender 28's tree. -/
def opRounds (n : Nat) : Nat → CTree
  | 0 => roundTree n
  | k + 1 => opRound (opRounds n k)

end U2

/-- The tree of input `n`: `n+1` rounds of higher-order universe operators. -/
def operatorTree (n : Nat) : CTree := U2.opRounds n (n + 1)

end BusyLean.Ordinal
