import BusyLean.Contender59
import BusyLean.Comparison58

/-! # Contender 59: comparison theorems -/

namespace BusyLean.Ordinal

/-- Every level of the tower's number closure strictly dominates its oracle and argument. -/
theorem lt_towerT (P : List TL.Ty) (σ : TL.Env P) :
    ∀ (a : CTree) (g : Nat → Nat) (m : Nat),
      g m < (towerT P σ a).2 g m ∧ m < (towerT P σ a).2 g m := by
  intro a
  induction a with
  | zero => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩
  | succ a _ => intro g m; exact ⟨oracle_lt_numLift _ _ g m, input_lt_numLift _ _ g m⟩
  | lim f ih =>
      intro g m
      show g m < maxUpTo (fun i => (towerT P σ (f i)).2 g m) m ∧
        m < maxUpTo (fun i => (towerT P σ (f i)).2 g m) m
      have h0 := le_maxUpTo (fun i => (towerT P σ (f i)).2 g m) (Nat.zero_le m)
      exact ⟨Nat.lt_of_lt_of_le (ih 0 g m).1 h0, Nat.lt_of_lt_of_le (ih 0 g m).2 h0⟩
  | supL _ _ => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩
  | supH _ _ => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩

end BusyLean.Ordinal

namespace BusyLean

theorem input_lt_family58 (n : Nat) : n < family58 n :=
  Nat.lt_trans (input_lt_F58 n) (input_lt_F58 (F58 n))

/-- At every input, `F59` exceeds Contender 58's family. -/
theorem family58_lt_F59 (n : Nat) : family58 n < F59 n := by
  have hS := Ordinal.lt_towerT prims54 (primEnv54 (family58 n) family58)
    (towerTreeT (family58 n)) family58
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (towerTreeT (family58 n))
    (family58 n)).1
  exact Nat.lt_trans (input_lt_family58 (family58 n)) (Nat.lt_of_lt_of_le (hS (family58 n)).1 h1)

theorem input_lt_F59 (n : Nat) : n < F59 n :=
  Nat.lt_trans (input_lt_family58 n) (family58_lt_F59 n)

/-- **The required comparison**: Contender 58 is strictly smaller than Contender 59. -/
theorem contender_58_lt_contender_59 : contender_58 < contender_59 :=
  Nat.lt_trans (family58_lt_F59 42) (input_lt_F59 (F59 42))

theorem contender_57_lt_contender_59 : contender_57 < contender_59 :=
  Nat.lt_trans contender_57_lt_contender_58 contender_58_lt_contender_59

end BusyLean
