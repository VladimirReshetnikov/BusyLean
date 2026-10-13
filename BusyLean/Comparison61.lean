import BusyLean.Contender61
import BusyLean.Comparison60

/-! # Contender 61: comparison theorems -/

namespace BusyLean.Ordinal

theorem le_num2Lift_of {P : List PTL2.Ty} {σ : PTL2.Env P} {g : Nat → Nat} {m x : Nat}
    (h : x ≤ BigNumber.maxN (g m)
      (BigNumber.maximum id (PTL2.natsUpTo (.arr .nat .nat :: P) (g, σ) m))) :
    x < num2Lift P σ g m := by
  show x < m + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ m + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 m) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_num2Lift (P : List PTL2.Ty) (σ : PTL2.Env P) (g : Nat → Nat) (m : Nat) :
    g m < num2Lift P σ g m :=
  le_num2Lift_of (BigNumber.le_maxN_left _ _)

theorem input_lt_num2Lift (P : List PTL2.Ty) (σ : PTL2.Env P) (g : Nat → Nat) (m : Nat) :
    m < num2Lift P σ g m := by
  show m < m + 1 + _
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_add_right _ _)

/-- Every closed `nat` program over the primitives plus `g` is below the closure. -/
theorem program_lt_num2Lift (P : List PTL2.Ty) (σ : PTL2.Env P) (g : Nat → Nat) {m v : Nat}
    (hv : v ∈ PTL2.natsUpTo (.arr .nat .nat :: P) (g, σ) m) : v < num2Lift P σ g m :=
  le_num2Lift_of (Nat.le_trans (W.le_maximum id hv) (BigNumber.le_maxN_right _ _))

end BusyLean.Ordinal

namespace BusyLean

theorem input_lt_family60 (n : Nat) : n < family60 n :=
  Nat.lt_trans (input_lt_F60 n) (input_lt_F60 (F60 n))

theorem oracle_lt_towerProgClosure (N : Nat) (g : Nat → Nat) (m : Nat) :
    g m < towerProgClosure N g m :=
  Ordinal.oracle_lt_num2Lift _ _ g m

theorem input_lt_towerProgClosure (N : Nat) (g : Nat → Nat) (m : Nat) :
    m < towerProgClosure N g m :=
  Ordinal.input_lt_num2Lift _ _ g m

/-- At every input, `F61` exceeds Contender 60's family. -/
theorem family60_lt_F61 (n : Nat) : family60 n < F61 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt
    (input_lt_towerProgClosure (family60 n) family60 x)) (towerProgTree (family60 n)) (family60 n)).1
  have h2 := oracle_lt_towerProgClosure (family60 n) family60 (family60 n)
  exact Nat.lt_trans (input_lt_family60 (family60 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F61 (n : Nat) : n < F61 n :=
  Nat.lt_trans (input_lt_family60 n) (family60_lt_F61 n)

/-- **The required comparison**: Contender 60 is strictly smaller than Contender 61. -/
theorem contender_60_lt_contender_61 : contender_60 < contender_61 :=
  Nat.lt_trans (family60_lt_F61 42) (input_lt_F61 (F61 42))

theorem contender_59_lt_contender_61 : contender_59 < contender_61 :=
  Nat.lt_trans contender_59_lt_contender_60 contender_60_lt_contender_61

end BusyLean
