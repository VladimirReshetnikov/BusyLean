import BusyLean.Contender45
import BusyLean.Comparison44

/-! # Contender 45: comparison and live-branch theorems -/

namespace BusyLean

/-- `family44` is strictly inflationary. -/
theorem input_lt_family44 (n : Nat) : n < family44 n :=
  Nat.lt_trans (input_lt_F44 n) (input_lt_F44 (F44 n))

/-- At every input, `F45` strictly exceeds Contender 44's family. -/
theorem family44_lt_F45 (n : Nat) : family44 n < F45 n :=
  Nat.lt_of_lt_of_le (input_lt_family44 (family44 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family44 x))
      (universalTree45 (family44 n)) (family44 n)).1

/-- The retained official Contender 44 tree is a live lower-bound branch of
`F45`. -/
theorem level_tree44_le_F45 (n : Nat) :
    Ordinal.hier family44 (levelTree44 (family44 n)) (family44 n) ≤ F45 n := by
  unfold F45 universalTree45
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier family44
      (if i = 0 then levelTree44 (family44 n)
       else Ordinal.universalBoostT (levelTree44 (family44 n))
         (base45 (family44 n)) (levelTree44 (family44 n)))
      (family44 n))
    (Nat.zero_le (family44 n))
  simpa [Ordinal.hier] using h

/-- The positive universal-reflection branch is also numerically live; the new
interpreter stack is not unreachable data hidden behind branch zero. -/
theorem universal_stack_le_F45 (n : Nat) :
    Ordinal.hier family44
      (Ordinal.universalBoostT (levelTree44 (family44 n))
        (base45 (family44 n)) (levelTree44 (family44 n)))
      (family44 n) ≤ F45 n := by
  unfold F45 universalTree45
  have h1 : 1 ≤ family44 n := by
    exact Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (Nat.zero_le n) (input_lt_family44 n))
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier family44
      (if i = 0 then levelTree44 (family44 n)
       else Ordinal.universalBoostT (levelTree44 (family44 n))
         (base45 (family44 n)) (levelTree44 (family44 n)))
      (family44 n))
    h1
  simpa [Ordinal.hier] using h

/-- `F45` is strictly inflationary. -/
theorem input_lt_F45 (n : Nat) : n < F45 n :=
  Nat.lt_trans (input_lt_family44 n) (family44_lt_F45 n)

/-- **The required comparison**: the official Contender 44 is strictly smaller
than Contender 45. -/
theorem contender_44_lt_contender_45 : contender_44 < contender_45 :=
  Nat.lt_trans (family44_lt_F45 42) (input_lt_F45 (F45 42))

/-- Convenient transitive comparisons. -/
theorem contender_43_lt_contender_45 : contender_43 < contender_45 :=
  Nat.lt_trans contender_43_lt_contender_44 contender_44_lt_contender_45

theorem contender_42_lt_contender_45 : contender_42 < contender_45 :=
  Nat.lt_trans contender_42_lt_contender_44 contender_44_lt_contender_45

end BusyLean
