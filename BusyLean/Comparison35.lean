import BusyLean.Contender35
import BusyLean.Comparison34

/-! # Contender 35: comparison theorems -/

namespace BusyLean

open BusyLean.W

/-- Any number bounded by the reflected maximum is strictly below the result. -/
theorem lt_reflectMetaFamily {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (FL.metavalue n (packFamily fs) n)
        (FL.metatreeLadderUpTo n))) :
    m < reflectMetaFamily fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every visible coordinate of the oracle family is strictly reflected. -/
theorem oracle_lt_reflectMetaFamily (fs : Family) {i n : Nat}
    (hi : i ≤ n) : fs i n < reflectMetaFamily fs n :=
  lt_reflectMetaFamily
    (Nat.le_trans (le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every enumerated program value is strictly reflected. -/
theorem metavalue_lt_reflectMetaFamily (fs : Family) {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.metaLanguageTree n))}
    (ht : t ∈ FL.metatreeLadderUpTo n) :
    FL.metavalue n (packFamily fs) n t < reflectMetaFamily fs n :=
  lt_reflectMetaFamily
    (Nat.le_trans
      (le_maximum (FL.metavalue n (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- The metalanguage reflection transformer is progressive. -/
theorem metaTransformer_progressive : Progressive metaTransformer :=
  fun seed _ _ _ hi => oracle_lt_reflectMetaFamily seed hi

/-- At every input, `F35` exceeds Contender 34's full family. -/
theorem family34_lt_F35 (n : Nat) : family34 n < F35 n :=
  ((wDiagonalLift_preservesProgressive (schedule35 n) (rank35 n))
    metaTransformer metaTransformer_progressive)
    (fun _ => family34) 0 n n (Nat.zero_le n)

/-- One raw metalanguage-reflection step is below the W-ranked lift. -/
theorem raw_meta_reflection_lt_F35 (n : Nat) :
    reflectMetaFamily (fun _ => family34) n < F35 n :=
  (wDiagonalLift_strictlyInflationary (schedule35 n) (rank35 n))
    metaTransformer metaTransformer_progressive
      (fun _ => family34) n n n (Nat.le_refl n)

/-- Every enumerated metalanguage-tree program, run with the packed seed, is
below `F35 n`. -/
theorem metavalue_lt_F35 {n : Nat}
    {t : FL.CTm (Ordinal.Addr (Ordinal.metaLanguageTree n))}
    (ht : t ∈ FL.metatreeLadderUpTo n) :
    FL.metavalue n (packFamily (fun _ => family34)) n t < F35 n :=
  Nat.lt_trans (metavalue_lt_reflectMetaFamily (fun _ => family34) ht)
    (raw_meta_reflection_lt_F35 n)

/-- The input is below the seed family. -/
theorem input_lt_family34 (n : Nat) : n < family34 n :=
  Nat.lt_trans (input_lt_F34 n) (input_lt_F34 (F34 n))

/-- `F35` is strictly inflationary on natural inputs. -/
theorem input_lt_F35 (n : Nat) : n < F35 n :=
  Nat.lt_trans (input_lt_family34 n) (family34_lt_F35 n)

/-- **Required comparison:** Contender 34 is strictly below Contender 35. -/
theorem contender_34_lt_contender_35 : contender_34 < contender_35 :=
  Nat.lt_trans (family34_lt_F35 42) (input_lt_F35 (F35 42))

/-- A useful transitive comparison with the preceding accepted contender. -/
theorem contender_33_lt_contender_35 : contender_33 < contender_35 :=
  Nat.lt_trans contender_33_lt_contender_34 contender_34_lt_contender_35

end BusyLean
