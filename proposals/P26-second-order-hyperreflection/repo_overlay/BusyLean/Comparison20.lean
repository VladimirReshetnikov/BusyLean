import BusyLean.Contender20
import BusyLean.SecondOrderReflectionFacts
import BusyLean.Comparison19

/-! # Contender 20: comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- The embedded first-order diagonal lift has both properties required by the
second-order hierarchy. -/
theorem baseLift20_good (n : Nat) : GoodLift (baseLift20 n) :=
  ⟨diagonalLift_preservesProgressive (schedule20 n) (rank20 n),
    diagonalLift_strictlyInflationary (schedule20 n) (rank20 n)⟩

/-- The embedded first-order transformer is progressive. -/
theorem firstOrderTransformer20_progressive (n : Nat) :
    Progressive (baseLift20 n lTransformer) :=
  (baseLift20_good n).1 lTransformer lTransformer_progressive

/-- The complete predecessor family is below the embedded first-order layer. -/
theorem family19_lt_firstOrder20 (n : Nat) :
    family19 n < firstOrder20 n :=
  firstOrderTransformer20_progressive n
    (fun _ => family19) 0 n n (Nat.zero_le n)

/-- The second-order hierarchy maps the embedded first-order lift to a good
lift. -/
theorem hyperLift20_good (n : Nat) :
    GoodLift
      (diagonalHyperLift (schedule20 n) (rank20 n) (baseLift20 n)) :=
  (diagonalHyperLift_preservesGoodLifts (schedule20 n) (rank20 n))
    (baseLift20 n) (baseLift20_good n)

/-- The second-order transformer used by `F20` is progressive. -/
theorem secondOrderTransformer20_progressive (n : Nat) :
    Progressive
      (diagonalHyperLift (schedule20 n) (rank20 n)
        (baseLift20 n) lTransformer) :=
  (hyperLift20_good n).1 lTransformer lTransformer_progressive

/-- The full embedded first-order layer is strictly below `F20`. -/
theorem firstOrder20_lt_F20 (n : Nat) : firstOrder20 n < F20 n :=
  (diagonalHyperLift_strictlyLiftInflationary
      (schedule20 n) (rank20 n))
    (baseLift20 n) (baseLift20_good n)
    lTransformer lTransformer_progressive
    (fun _ => family19) n n n (Nat.le_refl n)

/-- At every input, `F20` strictly exceeds Contender 19's entire family, with a
formal intermediate witness consisting of a complete first-order diagonal
layer. -/
theorem family19_lt_F20 (n : Nat) : family19 n < F20 n :=
  Nat.lt_trans (family19_lt_firstOrder20 n) (firstOrder20_lt_F20 n)

/-- Every input is below Contender 19's family. -/
theorem input_lt_family19 (n : Nat) : n < family19 n :=
  Nat.lt_trans (input_lt_F19 n) (input_lt_F19 (F19 n))

/-- Every input is below the new family. -/
theorem input_lt_F20 (n : Nat) : n < F20 n :=
  Nat.lt_trans (input_lt_family19 n) (family19_lt_F20 n)

/-- **The required comparison:** Contender 19 is strictly smaller than
Contender 20. -/
theorem contender_19_lt_contender_20 : contender_19 < contender_20 :=
  Nat.lt_trans (family19_lt_F20 42) (input_lt_F20 (F20 42))

/-- A convenience corollary for the preceding accepted contender. -/
theorem contender_18_lt_contender_20 : contender_18 < contender_20 :=
  Nat.lt_trans contender_18_lt_contender_19 contender_19_lt_contender_20

end BusyLean
