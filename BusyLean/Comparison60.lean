import BusyLean.Contender60
import BusyLean.Comparison59

/-! # Contender 60: comparison theorems -/

namespace BusyLean.Ordinal

theorem lt_towerH (P : List TL.Ty) (σ : TL.Env P) (H : CTree → Closures) :
    ∀ (a : CTree) (g : Nat → Nat) (m : Nat),
      g m < (towerH P σ H a).2 g m ∧ m < (towerH P σ H a).2 g m := by
  intro a
  induction a with
  | zero => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩
  | succ a _ => intro g m; exact ⟨oracle_lt_numLift _ _ g m, input_lt_numLift _ _ g m⟩
  | lim f ih =>
      intro g m
      show g m < maxUpTo (fun i => (towerH P σ H (f i)).2 g m) m ∧
        m < maxUpTo (fun i => (towerH P σ H (f i)).2 g m) m
      have h0 := le_maxUpTo (fun i => (towerH P σ H (f i)).2 g m) (Nat.zero_le m)
      exact ⟨Nat.lt_of_lt_of_le (ih 0 g m).1 h0, Nat.lt_of_lt_of_le (ih 0 g m).2 h0⟩
  | supL _ _ => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩
  | supH _ _ => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩

/-- Every level and height of the hierarchy strictly dominates its oracle and argument. -/
theorem lt_upLevels (P : List TL.Ty) (σ : TL.Env P) :
    ∀ (k t : CTree) (g : Nat → Nat) (m : Nat),
      g m < (upLevels P σ k t).2 g m ∧ m < (upLevels P σ k t).2 g m := by
  intro k
  induction k with
  | zero => intro t g m; exact lt_towerT P σ t g m
  | succ k _ => intro t g m; exact lt_towerH P σ _ t g m
  | lim f ih =>
      intro t g m
      show g m < maxUpTo (fun i => (upLevels P σ (f i) t).2 g m) m ∧
        m < maxUpTo (fun i => (upLevels P σ (f i) t).2 g m) m
      have h0 := le_maxUpTo (fun i => (upLevels P σ (f i) t).2 g m) (Nat.zero_le m)
      exact ⟨Nat.lt_of_lt_of_le (ih 0 t g m).1 h0, Nat.lt_of_lt_of_le (ih 0 t g m).2 h0⟩
  | supL _ _ => intro t g m; exact lt_towerT P σ t g m
  | supH _ _ => intro t g m; exact lt_towerT P σ t g m

end BusyLean.Ordinal

namespace BusyLean

theorem input_lt_family59 (n : Nat) : n < family59 n :=
  Nat.lt_trans (input_lt_F59 n) (input_lt_F59 (F59 n))

/-- At every input, `F60` exceeds Contender 59's family. -/
theorem family59_lt_F60 (n : Nat) : family59 n < F60 n := by
  have hS := Ordinal.lt_upLevels prims54 (primEnv54 (family59 n) family59)
    (upTree (family59 n)) (upTree (family59 n)) family59
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (upTree (family59 n))
    (family59 n)).1
  exact Nat.lt_trans (input_lt_family59 (family59 n)) (Nat.lt_of_lt_of_le (hS (family59 n)).1 h1)

theorem input_lt_F60 (n : Nat) : n < F60 n :=
  Nat.lt_trans (input_lt_family59 n) (family59_lt_F60 n)

/-- **The required comparison**: Contender 59 is strictly smaller than Contender 60. -/
theorem contender_59_lt_contender_60 : contender_59 < contender_60 :=
  Nat.lt_trans (family59_lt_F60 42) (input_lt_F60 (F60 42))

theorem contender_58_lt_contender_60 : contender_58 < contender_60 :=
  Nat.lt_trans contender_58_lt_contender_59 contender_59_lt_contender_60

end BusyLean
