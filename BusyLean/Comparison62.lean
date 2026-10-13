import BusyLean.Contender62
import BusyLean.Comparison61

/-! # Contender 62: comparison theorems -/

namespace BusyLean.Ordinal

/-- Every level of the stacked number closure strictly dominates its oracle and argument. -/
theorem lt_stack2 (P : List PTL2.Ty) (σ : PTL2.Env P) :
    ∀ (a : CTree) (g : Nat → Nat) (m : Nat),
      g m < (stack2 P σ a).2 g m ∧ m < (stack2 P σ a).2 g m := by
  intro a
  induction a with
  | zero => intro g m; exact ⟨oracle_lt_num2Lift P σ g m, input_lt_num2Lift P σ g m⟩
  | succ a _ => intro g m; exact ⟨oracle_lt_num2Lift _ _ g m, input_lt_num2Lift _ _ g m⟩
  | lim f ih =>
      intro g m
      show g m < maxUpTo (fun i => (stack2 P σ (f i)).2 g m) m ∧
        m < maxUpTo (fun i => (stack2 P σ (f i)).2 g m) m
      have h0 := le_maxUpTo (fun i => (stack2 P σ (f i)).2 g m) (Nat.zero_le m)
      exact ⟨Nat.lt_of_lt_of_le (ih 0 g m).1 h0, Nat.lt_of_lt_of_le (ih 0 g m).2 h0⟩
  | supL _ _ => intro g m; exact ⟨oracle_lt_num2Lift P σ g m, input_lt_num2Lift P σ g m⟩
  | supH _ _ => intro g m; exact ⟨oracle_lt_num2Lift P σ g m, input_lt_num2Lift P σ g m⟩

end BusyLean.Ordinal

namespace BusyLean

theorem input_lt_family61 (n : Nat) : n < family61 n :=
  Nat.lt_trans (input_lt_F61 n) (input_lt_F61 (F61 n))

/-- At every input, `F62` exceeds Contender 61's family. -/
theorem family61_lt_F62 (n : Nat) : family61 n < F62 n := by
  have hS := Ordinal.lt_stack2 prims61 (primEnv61 (family61 n) family61)
    (stack2Tree (family61 n)) family61
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (stack2Tree (family61 n))
    (family61 n)).1
  exact Nat.lt_trans (input_lt_family61 (family61 n)) (Nat.lt_of_lt_of_le (hS (family61 n)).1 h1)

theorem input_lt_F62 (n : Nat) : n < F62 n :=
  Nat.lt_trans (input_lt_family61 n) (family61_lt_F62 n)

/-- **The required comparison**: Contender 61 is strictly smaller than Contender 62. -/
theorem contender_61_lt_contender_62 : contender_61 < contender_62 :=
  Nat.lt_trans (family61_lt_F62 42) (input_lt_F62 (F62 42))

theorem contender_60_lt_contender_62 : contender_60 < contender_62 :=
  Nat.lt_trans contender_60_lt_contender_61 contender_61_lt_contender_62

end BusyLean
