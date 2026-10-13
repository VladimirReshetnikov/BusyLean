import BusyLean.Contender54
import BusyLean.Comparison53

/-! # Contender 54: comparison theorems -/

namespace BusyLean

/-- Contender 53's family is strictly inflationary. -/
theorem input_lt_family53 (n : Nat) : n < family53 n :=
  Nat.lt_trans (input_lt_F53 n) (input_lt_F53 (F53 n))

/-- A positive number of iterations of a strictly inflationary function is
strictly above its input. -/
theorem lt_iterN_of_pos {g : Nat → Nat} (hg : ∀ x, x < g x) :
    ∀ {k x : Nat}, 0 < k → x < Ordinal.iterN g k x
  | 0, _, hk => by simp at hk
  | k + 1, x, _ =>
      Nat.lt_of_lt_of_le (hg x)
        (Ordinal.le_iterN (fun y => Nat.le_of_lt (hg y)) k (g x))

/-- The transparent branch of `F54` contains an entire `family53` orbit of
length `family53 n`, not merely one application of the old family. -/
theorem iter_family53_le_F54 (n : Nat) :
    Ordinal.iterN family53 (family53 n) (family53 n) ≤ F54 n := by
  have h := Ordinal.le_maxUpTo
    (fun i => largeElim family53
      (if i = 0 then ramify .zero 1
       else ramify (stackTree (family53 n)) i)
      (family53 n))
    (Nat.zero_le (family53 n))
  simpa [F54, largeTypeTree, ramify] using h

/-- The genuinely new branch at the largest inspected index is present in
`F54`: semantic order is raised by `2 * family53 n` above the full stacked
tree. -/
theorem ramified_core_le_F54 (n : Nat) :
    largeElim family53
      (ramify (stackTree (family53 n)) (family53 n))
      (family53 n) ≤ F54 n := by
  have hpos : 0 < family53 n :=
    Nat.lt_of_le_of_lt (Nat.zero_le n) (input_lt_family53 n)
  have hne : family53 n ≠ 0 := Nat.ne_of_gt hpos
  have h := Ordinal.le_maxUpTo
    (fun i => largeElim family53
      (if i = 0 then ramify .zero 1
       else ramify (stackTree (family53 n)) i)
      (family53 n))
    (Nat.le_refl (family53 n))
  simpa [F54, largeTypeTree, hne] using h

/-- At every input, `F54` exceeds Contender 53's family. -/
theorem family53_lt_F54 (n : Nat) : family53 n < F54 n := by
  have hpos : 0 < family53 n :=
    Nat.lt_of_le_of_lt (Nat.zero_le n) (input_lt_family53 n)
  exact Nat.lt_of_lt_of_le
    (lt_iterN_of_pos (fun x => input_lt_family53 x) hpos)
    (iter_family53_le_F54 n)

/-- `F54` is strictly inflationary. -/
theorem input_lt_F54 (n : Nat) : n < F54 n :=
  Nat.lt_trans (input_lt_family53 n) (family53_lt_F54 n)

/-- A stronger quantitative comparison: Contender 54 exceeds an orbit of
Contender 53's whole family whose length and starting point are both
`contender_53`. -/
theorem iter_contender_53_lt_contender_54 :
    Ordinal.iterN family53 contender_53 contender_53 < contender_54 :=
  Nat.lt_of_le_of_lt (iter_family53_le_F54 42)
    (input_lt_F54 (F54 42))

/-- **The required comparison:** Contender 53 is strictly smaller than
Contender 54. -/
theorem contender_53_lt_contender_54 : contender_53 < contender_54 :=
  Nat.lt_trans (family53_lt_F54 42) (input_lt_F54 (F54 42))

/-- Consequently every earlier integrated contender is also smaller. -/
theorem contender_52_lt_contender_54 : contender_52 < contender_54 :=
  Nat.lt_trans contender_52_lt_contender_53 contender_53_lt_contender_54

end BusyLean
