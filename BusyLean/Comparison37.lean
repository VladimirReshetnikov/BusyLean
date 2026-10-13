import BusyLean.Contender37
import BusyLean.Comparison36

/-! # Contender 37: formal comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- Anything below the reflected maximum is strictly below the reflection. -/
theorem lt_reflectOMFamily {fs : Family} {n m : Nat}
    (h : m <= BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.omvalue n (packFamily fs) n) (FL.omLadderUpTo n))) :
    m < reflectOMFamily fs n := by
  show m < n + 1 + _
  have hM : forall M : Nat, M + 1 <= n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible coordinate of the oracle family is strictly reflected. -/
theorem oracle_lt_reflectOMFamily (fs : Family) {i n : Nat} (hi : i <= n) :
    fs i n < reflectOMFamily fs n :=
  lt_reflectOMFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every enumerated ladder-program value is strictly reflected. -/
theorem omvalue_lt_reflectOMFamily (fs : Family) {n : Nat}
    {t : FL.CTm (Ordinal.Addr (operatorMetaTree n))}
    (ht : t ∈ FL.omLadderUpTo n) :
    FL.omvalue n (packFamily fs) n t < reflectOMFamily fs n :=
  lt_reflectOMFamily
    (Nat.le_trans (le_maximum (FL.omvalue n (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- `omTransformer` is progressive, as required by the amplifier. -/
theorem omTransformer_progressive : Progressive omTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectOMFamily seed hi

/-- At every input, `F37` exceeds Contender 36's family. -/
theorem family36_lt_F37 (n : Nat) : family36 n < F37 n :=
  ((wDiagonalLift_preservesProgressive (schedule37 n) (rank37 n))
    omTransformer omTransformer_progressive)
    (fun _ => family36) 0 n n (Nat.zero_le n)

/-- Even the raw first reflection lies below the full W-ranked lift. -/
theorem raw_reflection_lt_F37 (n : Nat) :
    reflectOMFamily (fun _ => family36) n < F37 n :=
  (wDiagonalLift_strictlyInflationary (schedule37 n) (rank37 n))
    omTransformer omTransformer_progressive (fun _ => family36) n n n (Nat.le_refl n)

/-- Every bounded program in the new ladder is below `F37 n`. -/
theorem omvalue_lt_F37 {n : Nat}
    {t : FL.CTm (Ordinal.Addr (operatorMetaTree n))}
    (ht : t ∈ FL.omLadderUpTo n) :
    FL.omvalue n (packFamily (fun _ => family36)) n t < F37 n :=
  Nat.lt_trans (omvalue_lt_reflectOMFamily (fun _ => family36) ht)
    (raw_reflection_lt_F37 n)

/-- The input is below the seed family at every argument. -/
theorem input_lt_family36 (n : Nat) : n < family36 n :=
  Nat.lt_trans (input_lt_F36 n) (input_lt_F36 (F36 n))

/-- The input is below `F37` at every argument. -/
theorem input_lt_F37 (n : Nat) : n < F37 n :=
  Nat.lt_trans (input_lt_family36 n) (family36_lt_F37 n)

/-- **Required comparison:** Contender 36 is strictly below Contender 37. -/
theorem contender_36_lt_contender_37 : contender_36 < contender_37 :=
  Nat.lt_trans (family36_lt_F37 42) (input_lt_F37 (F37 42))

/-- A transitive comparison with Contender 35. -/
theorem contender_35_lt_contender_37 : contender_35 < contender_37 :=
  Nat.lt_trans contender_35_lt_contender_36 contender_36_lt_contender_37

end BusyLean
