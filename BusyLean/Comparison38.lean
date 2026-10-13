import BusyLean.Contender38
import BusyLean.Comparison37

/-! # Contender 38: formal comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- Anything below the reflected maximum is strictly below the reflection. -/
theorem lt_reflectOM38Family {fs : Family} {n m : Nat}
    (h : m <= BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.om38value n (packFamily fs) n) (FL.om38LadderUpTo n))) :
    m < reflectOM38Family fs n := by
  show m < n + 1 + _
  have hM : forall M : Nat, M + 1 <= n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible coordinate of the oracle family is strictly reflected. -/
theorem oracle_lt_reflectOM38Family (fs : Family) {i n : Nat} (hi : i <= n) :
    fs i n < reflectOM38Family fs n :=
  lt_reflectOM38Family
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every enumerated ladder-program value is strictly reflected. -/
theorem om38value_lt_reflectOM38Family (fs : Family) {n : Nat}
    {t : FL.CTm (Ordinal.Addr (operatorMetaTree38 n))}
    (ht : t ∈ FL.om38LadderUpTo n) :
    FL.om38value n (packFamily fs) n t < reflectOM38Family fs n :=
  lt_reflectOM38Family
    (Nat.le_trans (le_maximum (FL.om38value n (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- `om38Transformer` is progressive, as required by the amplifier. -/
theorem om38Transformer_progressive : Progressive om38Transformer :=
  fun seed _ _ _ hi => oracle_lt_reflectOM38Family seed hi

/-- At every input, `F38` exceeds Contender 37's family. -/
theorem family37_lt_F38 (n : Nat) : family37 n < F38 n :=
  ((wDiagonalLift_preservesProgressive (schedule38 n) (rank38 n))
    om38Transformer om38Transformer_progressive)
    (fun _ => family37) 0 n n (Nat.zero_le n)

/-- Even the raw first reflection lies below the full W-ranked lift. -/
theorem raw_reflection_lt_F38 (n : Nat) :
    reflectOM38Family (fun _ => family37) n < F38 n :=
  (wDiagonalLift_strictlyInflationary (schedule38 n) (rank38 n))
    om38Transformer om38Transformer_progressive (fun _ => family37) n n n (Nat.le_refl n)

/-- Every bounded program in the new ladder is below `F38 n`. -/
theorem om38value_lt_F38 {n : Nat}
    {t : FL.CTm (Ordinal.Addr (operatorMetaTree38 n))}
    (ht : t ∈ FL.om38LadderUpTo n) :
    FL.om38value n (packFamily (fun _ => family37)) n t < F38 n :=
  Nat.lt_trans (om38value_lt_reflectOM38Family (fun _ => family37) ht)
    (raw_reflection_lt_F38 n)

/-- The input is below the seed family at every argument. -/
theorem input_lt_family37 (n : Nat) : n < family37 n :=
  Nat.lt_trans (input_lt_F37 n) (input_lt_F37 (F37 n))

/-- The input is below `F38` at every argument. -/
theorem input_lt_F38 (n : Nat) : n < F38 n :=
  Nat.lt_trans (input_lt_family37 n) (family37_lt_F38 n)

/-- **Required comparison:** Contender 37 is strictly below Contender 38. -/
theorem contender_37_lt_contender_38 : contender_37 < contender_38 :=
  Nat.lt_trans (family37_lt_F38 42) (input_lt_F38 (F38 42))

/-- A transitive comparison with Contender 36. -/
theorem contender_36_lt_contender_38 : contender_36 < contender_38 :=
  Nat.lt_trans contender_36_lt_contender_37 contender_37_lt_contender_38

end BusyLean
