import BusyLean.Contender42
import BusyLean.Comparison41

/-! # Contender 42: comparison theorems -/

namespace BusyLean

/-- `family41` is strictly inflationary. -/
theorem input_lt_family41 (n : Nat) : n < family41 n :=
  Nat.lt_trans (input_lt_F41 n) (input_lt_F41 (F41 n))

/-- At every input, `F42` strictly exceeds Contender 41's family. -/
theorem family41_lt_F42 (n : Nat) : family41 n < F42 n :=
  Nat.lt_of_lt_of_le (input_lt_family41 (family41 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family41 x))
      (universalTree (family41 n)) (family41 n)).1

/-- The positive universal-reflection branch is numerically live: its hierarchy
value at the same base and index is a lower bound for `F42`.  Thus the new
interpreter stack is not merely unreachable data hidden behind branch zero. -/
theorem universal_stack_le_F42 (n : Nat) :
    Ordinal.hier family41
      (Ordinal.universalBoostT (readerTree (family41 n))
        (base42 (family41 n)) (readerTree (family41 n)))
      (family41 n) ≤ F42 n := by
  unfold F42 universalTree
  have h1 : 1 ≤ family41 n := by
    exact Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (Nat.zero_le n) (input_lt_family41 n))
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier family41
      (if i = 0 then readerTree (family41 n)
       else Ordinal.universalBoostT (readerTree (family41 n))
         (base42 (family41 n)) (readerTree (family41 n)))
      (family41 n))
    h1
  simpa [Ordinal.hier] using h

/-- `F42` is strictly inflationary. -/
theorem input_lt_F42 (n : Nat) : n < F42 n :=
  Nat.lt_trans (input_lt_family41 n) (family41_lt_F42 n)

/-- **The required comparison**: Contender 41 is strictly smaller than
Contender 42. -/
theorem contender_41_lt_contender_42 : contender_41 < contender_42 :=
  Nat.lt_trans (family41_lt_F42 42) (input_lt_F42 (F42 42))

/-- A convenient transitive comparison with Contender 40. -/
theorem contender_40_lt_contender_42 : contender_40 < contender_42 :=
  Nat.lt_trans contender_40_lt_contender_41 contender_41_lt_contender_42

end BusyLean
