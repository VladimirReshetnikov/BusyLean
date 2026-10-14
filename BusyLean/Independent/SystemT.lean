import BusyLean.Contender5

/-!
# Independent tower, rung 2: the largest System T numeral of depth 42

The second rung is samuelgruetter's Contender 5 of the original Coq contest:
the largest value of a raw STLC + natural-recursion term (Gödel's System T) of
syntax depth at most 42. The idea is the **busy beaver of a total
higher-type language**: primitive recursion at all finite types, maximized
over every program of bounded size.

The definition is the exact port in `BusyLean/Contender5.lean`, which depends
on nothing else. **Do not evaluate `contender_2`.**
-/

namespace BusyLean.Indep

/-- **Rung 2** (Contender 5 of the Coq contest). -/
def contender_2 : Nat := C5.largestSTLCNatRecNatOfDepth 42

end BusyLean.Indep
