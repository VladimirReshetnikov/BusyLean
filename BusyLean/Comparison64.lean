import BusyLean.Contender64
import BusyLean.Comparison63

/-! # Contender 64: comparison theorems -/

namespace BusyLean

/-- Every level of the tower's number closure strictly dominates its oracle and argument. -/
theorem lt_tower2 (N : Nat) (g0 : Nat → Nat) :
    ∀ (a : Ordinal.CTree) (g : Nat → Nat) (m : Nat),
      g m < (tower2 N g0 a).2 g m ∧ m < (tower2 N g0 a).2 g m := by
  intro a
  induction a with
  | zero => intro g m; exact ⟨Ordinal.oracle_lt_num2Lift _ _ g m, Ordinal.input_lt_num2Lift _ _ g m⟩
  | succ a _ => intro g m; exact ⟨Ordinal.oracle_lt_num2Lift _ _ g m, Ordinal.input_lt_num2Lift _ _ g m⟩
  | lim f ih =>
      intro g m
      show g m < Ordinal.maxUpTo (fun i => (tower2 N g0 (f i)).2 g m) m ∧
        m < Ordinal.maxUpTo (fun i => (tower2 N g0 (f i)).2 g m) m
      have h0 := Ordinal.le_maxUpTo (fun i => (tower2 N g0 (f i)).2 g m) (Nat.zero_le m)
      exact ⟨Nat.lt_of_lt_of_le (ih 0 g m).1 h0, Nat.lt_of_lt_of_le (ih 0 g m).2 h0⟩
  | supL _ _ => intro g m; exact ⟨Ordinal.oracle_lt_num2Lift _ _ g m, Ordinal.input_lt_num2Lift _ _ g m⟩
  | supH _ _ => intro g m; exact ⟨Ordinal.oracle_lt_num2Lift _ _ g m, Ordinal.input_lt_num2Lift _ _ g m⟩

theorem input_lt_family63 (n : Nat) : n < family63 n :=
  Nat.lt_trans (input_lt_F63 n) (input_lt_F63 (F63 n))

/-- At every input, `F64` exceeds Contender 63's family. -/
theorem family63_lt_F64 (n : Nat) : family63 n < F64 n := by
  have hS := lt_tower2 (family63 n) family63 (tower2Tree (family63 n)) family63
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (tower2Tree (family63 n))
    (family63 n)).1
  exact Nat.lt_trans (input_lt_family63 (family63 n)) (Nat.lt_of_lt_of_le (hS (family63 n)).1 h1)

theorem input_lt_F64 (n : Nat) : n < F64 n :=
  Nat.lt_trans (input_lt_family63 n) (family63_lt_F64 n)

/-- **The required comparison**: Contender 63 is strictly smaller than Contender 64. -/
theorem contender_63_lt_contender_64 : contender_63 < contender_64 :=
  Nat.lt_trans (family63_lt_F64 42) (input_lt_F64 (F64 42))

theorem contender_62_lt_contender_64 : contender_62 < contender_64 :=
  Nat.lt_trans contender_62_lt_contender_63 contender_63_lt_contender_64

end BusyLean
