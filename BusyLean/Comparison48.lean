import BusyLean.Contender48
import BusyLean.Comparison47

/-! # Contender 48: comparison and live-branch theorems -/

namespace BusyLean

/-- `family47` is strictly inflationary. -/
theorem input_lt_family47 (n : Nat) : n < family47 n :=
  Nat.lt_trans (input_lt_F47 n) (input_lt_F47 (F47 n))

/-- At every input, `F48` strictly exceeds Contender 47's family. -/
theorem family47_lt_F48 (n : Nat) : family47 n < F48 n :=
  Nat.lt_of_lt_of_le (input_lt_family47 (family47 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family47 x))
      (universalTree48 (family47 n)) (family47 n)).1

/-- The retained official Contender 47 tree is a live lower-bound branch. -/
theorem psi_tree47_le_F48 (n : Nat) :
    Ordinal.hier family47 (psiTree (family47 n)) (family47 n) ≤ F48 n := by
  unfold F48 universalTree48
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier family47
      (if i = 0 then psiTree (family47 n)
       else Ordinal.universalBoostT (psiTree (family47 n))
         (base48 (family47 n)) (psiTree (family47 n)))
      (family47 n))
    (Nat.zero_le (family47 n))
  simpa [Ordinal.hier] using h

/-- The positive universal-reflection branch is also numerically live. -/
theorem universal_stack_le_F48 (n : Nat) :
    Ordinal.hier family47
      (Ordinal.universalBoostT (psiTree (family47 n))
        (base48 (family47 n)) (psiTree (family47 n)))
      (family47 n) ≤ F48 n := by
  unfold F48 universalTree48
  have h1 : 1 ≤ family47 n := by
    exact Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (Nat.zero_le n) (input_lt_family47 n))
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier family47
      (if i = 0 then psiTree (family47 n)
       else Ordinal.universalBoostT (psiTree (family47 n))
         (base48 (family47 n)) (psiTree (family47 n)))
      (family47 n))
    h1
  simpa [Ordinal.hier] using h

/-- `F48` is strictly inflationary. -/
theorem input_lt_F48 (n : Nat) : n < F48 n :=
  Nat.lt_trans (input_lt_family47 n) (family47_lt_F48 n)

/-- **The required comparison**: Contender 47 is strictly smaller than
Contender 48. -/
theorem contender_47_lt_contender_48 : contender_47 < contender_48 :=
  Nat.lt_trans (family47_lt_F48 42) (input_lt_F48 (F48 42))

/-- Convenient transitive comparisons. -/
theorem contender_46_lt_contender_48 : contender_46 < contender_48 :=
  Nat.lt_trans contender_46_lt_contender_47 contender_47_lt_contender_48

theorem contender_45_lt_contender_48 : contender_45 < contender_48 :=
  Nat.lt_trans contender_45_lt_contender_47 contender_47_lt_contender_48

end BusyLean
