import BusyLean.Contender35
import BusyLean.Comparison34

/-! # Contender 35: formal comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- Anything below the reflected maximum is strictly below the reflection. -/
theorem lt_reflectOSFamily {fs : Family} {n m : Nat}
    (h : m <= BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.osvalue n (packFamily fs) n) (FL.ostreeLadderUpTo n))) :
    m < reflectOSFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 <= n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible coordinate of the oracle family is strictly reflected. -/
theorem oracle_lt_reflectOSFamily (fs : Family) {i n : Nat} (hi : i <= n) :
    fs i n < reflectOSFamily fs n :=
  lt_reflectOSFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every enumerated ladder-program value is strictly reflected. -/
theorem osvalue_lt_reflectOSFamily (fs : Family) {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.operatorStackedTree n))}
    (ht : t ∈ FL.ostreeLadderUpTo n) :
    FL.osvalue n (packFamily fs) n t < reflectOSFamily fs n :=
  lt_reflectOSFamily
    (Nat.le_trans (le_maximum (FL.osvalue n (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- `osTransformer` is progressive, the hypothesis needed by the amplifier. -/
theorem osTransformer_progressive : Progressive osTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectOSFamily seed hi

/-- At every input, `F35` exceeds Contender 34's family. -/
theorem family34_lt_F35 (n : Nat) : family34 n < F35 n :=
  ((wDiagonalLift_preservesProgressive (schedule35 n) (rank35 n))
    osTransformer osTransformer_progressive)
    (fun _ => family34) 0 n n (Nat.zero_le n)

/-- Even the raw first reflection lies below the full W-ranked lift. -/
theorem raw_reflection_lt_F35 (n : Nat) :
    reflectOSFamily (fun _ => family34) n < F35 n :=
  (wDiagonalLift_strictlyInflationary (schedule35 n) (rank35 n))
    osTransformer osTransformer_progressive (fun _ => family34) n n n (Nat.le_refl n)

/-- Every bounded program in the new ladder is below `F35 n`. -/
theorem osvalue_lt_F35 {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.operatorStackedTree n))}
    (ht : t ∈ FL.ostreeLadderUpTo n) :
    FL.osvalue n (packFamily (fun _ => family34)) n t < F35 n :=
  Nat.lt_trans (osvalue_lt_reflectOSFamily (fun _ => family34) ht)
    (raw_reflection_lt_F35 n)

/-- The input is below the seed family at every argument. -/
theorem input_lt_family34 (n : Nat) : n < family34 n :=
  Nat.lt_trans (input_lt_F34 n) (input_lt_F34 (F34 n))

/-- The input is below `F35` at every argument. -/
theorem input_lt_F35 (n : Nat) : n < F35 n :=
  Nat.lt_trans (input_lt_family34 n) (family34_lt_F35 n)

/-- **Required comparison:** Contender 34 is strictly below Contender 35. -/
theorem contender_34_lt_contender_35 : contender_34 < contender_35 :=
  Nat.lt_trans (family34_lt_F35 42) (input_lt_F35 (F35 42))

/-- A convenient transitive comparison with the preceding accepted contender. -/
theorem contender_33_lt_contender_35 : contender_33 < contender_35 :=
  Nat.lt_trans contender_33_lt_contender_34 contender_34_lt_contender_35

end BusyLean
