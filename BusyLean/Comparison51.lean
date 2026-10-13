import BusyLean.Contender51
import BusyLean.Comparison50

/-! # Contender 51: comparison and live-branch theorems -/

namespace BusyLean

/-- `family50` is strictly inflationary. -/
theorem input_lt_family50 (n : Nat) : n < family50 n :=
  Nat.lt_trans (input_lt_F50 n) (input_lt_F50 (F50 n))

/-- The ladder reader over the universal tree is strictly inflationary. -/
theorem input_lt_reader51 (N m : Nat) : m < reader51 N m :=
  input_lt_ladderReflect family50 (universalTree51 N) m

/-- At every input, `F51` strictly exceeds Contender 50's complete family. -/
theorem family50_lt_F51 (n : Nat) : family50 n < F51 n :=
  Nat.lt_of_lt_of_le (input_lt_reader51 (family50 n) (family50 n))
    (Ordinal.le_hier
      (fun x => Nat.le_of_lt (input_lt_reader51 (family50 n) x))
      (universalTree51 (family50 n)) (family50 n)).1

/-- The official tree used by Contenders 48--50 is a live lower-bound branch
of `F51`. -/
theorem official_tree_le_F51 (n : Nat) :
    Ordinal.hier (reader51 (family50 n))
      (levelIterTree (family50 n)) (family50 n) ≤ F51 n := by
  unfold F51 universalTree51
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier (reader51 (family50 n))
      (if i = 0 then levelIterTree (family50 n)
       else Ordinal.universalBoostT (levelIterTree (family50 n))
         (base51 (family50 n)) (levelIterTree (family50 n)))
      (family50 n))
    (Nat.zero_le (family50 n))
  simpa [Ordinal.hier] using h

/-- The positive universal-reflection branch is also numerically live. -/
theorem universal_stack_le_F51 (n : Nat) :
    Ordinal.hier (reader51 (family50 n))
      (Ordinal.universalBoostT (levelIterTree (family50 n))
        (base51 (family50 n)) (levelIterTree (family50 n)))
      (family50 n) ≤ F51 n := by
  unfold F51 universalTree51
  have h1 : 1 ≤ family50 n := by
    exact Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (Nat.zero_le n) (input_lt_family50 n))
  have h := Ordinal.le_maxUpTo
    (fun i => Ordinal.hier (reader51 (family50 n))
      (if i = 0 then levelIterTree (family50 n)
       else Ordinal.universalBoostT (levelIterTree (family50 n))
         (base51 (family50 n)) (levelIterTree (family50 n)))
      (family50 n))
    h1
  simpa [Ordinal.hier] using h

/-- `F51` is strictly inflationary. -/
theorem input_lt_F51 (n : Nat) : n < F51 n :=
  Nat.lt_trans (input_lt_family50 n) (family50_lt_F51 n)

/-- **The required comparison**: Contender 50 is strictly smaller than
Contender 51. -/
theorem contender_50_lt_contender_51 : contender_50 < contender_51 :=
  Nat.lt_trans (family50_lt_F51 42) (input_lt_F51 (F51 42))

/-- Convenient transitive comparisons. -/
theorem contender_49_lt_contender_51 : contender_49 < contender_51 :=
  Nat.lt_trans contender_49_lt_contender_50 contender_50_lt_contender_51

theorem contender_48_lt_contender_51 : contender_48 < contender_51 :=
  Nat.lt_trans contender_48_lt_contender_50 contender_50_lt_contender_51

end BusyLean
