import BusyLean.Contender43
import BusyLean.Comparison42

/-! # Contender 43: comparison and live-branch theorems -/

namespace BusyLean

/-- `family42` is strictly inflationary. -/
theorem input_lt_family42 (n : Nat) : n < family42 n :=
  Nat.lt_trans (input_lt_F42 n) (input_lt_F42 (F42 n))

/-- At every input, `F43` strictly exceeds Contender 42's family. -/
theorem family42_lt_F43 (n : Nat) : family42 n < F43 n :=
  Nat.lt_of_lt_of_le (input_lt_family42 (family42 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family42 x))
      (universalTree43 (family42 n)) (family42 n)).1

/-- The retained official Contender 42 collapse tree is a live lower-bound
branch of `F43`. -/
theorem collapse_tree_le_F43 (n : Nat) :
    Ordinal.hier family42 (collapseTree (family42 n)) (family42 n) ≤ F43 n := by
  unfold F43 universalTree43
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier family42
      (if i = 0 then collapseTree (family42 n)
       else Ordinal.universalBoostT (collapseTree (family42 n))
         (base43 (family42 n)) (collapseTree (family42 n)))
      (family42 n))
    (Nat.zero_le (family42 n))
  simpa [Ordinal.hier] using h

/-- The positive universal-reflection branch is also numerically live; the new
interpreter stack is not unreachable data hidden behind branch zero. -/
theorem universal_stack_le_F43 (n : Nat) :
    Ordinal.hier family42
      (Ordinal.universalBoostT (collapseTree (family42 n))
        (base43 (family42 n)) (collapseTree (family42 n)))
      (family42 n) ≤ F43 n := by
  unfold F43 universalTree43
  have h1 : 1 ≤ family42 n := by
    exact Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (Nat.zero_le n) (input_lt_family42 n))
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier family42
      (if i = 0 then collapseTree (family42 n)
       else Ordinal.universalBoostT (collapseTree (family42 n))
         (base43 (family42 n)) (collapseTree (family42 n)))
      (family42 n))
    h1
  simpa [Ordinal.hier] using h

/-- `F43` is strictly inflationary. -/
theorem input_lt_F43 (n : Nat) : n < F43 n :=
  Nat.lt_trans (input_lt_family42 n) (family42_lt_F43 n)

/-- **The required comparison**: the official Contender 42 is strictly smaller
than Contender 43. -/
theorem contender_42_lt_contender_43 : contender_42 < contender_43 :=
  Nat.lt_trans (family42_lt_F43 42) (input_lt_F43 (F43 42))

/-- Convenient transitive comparisons. -/
theorem contender_41_lt_contender_43 : contender_41 < contender_43 :=
  Nat.lt_trans contender_41_lt_contender_42 contender_42_lt_contender_43

theorem contender_40_lt_contender_43 : contender_40 < contender_43 :=
  Nat.lt_trans contender_40_lt_contender_42 contender_42_lt_contender_43

end BusyLean
