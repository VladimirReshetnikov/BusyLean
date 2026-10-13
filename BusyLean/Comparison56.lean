import BusyLean.Contender56
import BusyLean.Comparison55

/-! # Contender 56: comparison theorems -/

namespace BusyLean.Ordinal

/-- Every level of the joint number closure strictly dominates its oracle and argument. -/
theorem lt_jointStack (P : List TL.Ty) (σ : TL.Env P) :
    ∀ (a : CTree) (g : Nat → Nat) (m : Nat),
      g m < (jointStack P σ a).2 g m ∧ m < (jointStack P σ a).2 g m := by
  intro a
  induction a with
  | zero => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩
  | succ a _ => intro g m; exact ⟨oracle_lt_numLift _ _ g m, input_lt_numLift _ _ g m⟩
  | lim f ih =>
      intro g m
      show g m < maxUpTo (fun i => (jointStack P σ (f i)).2 g m) m ∧
        m < maxUpTo (fun i => (jointStack P σ (f i)).2 g m) m
      have h0 := le_maxUpTo (fun i => (jointStack P σ (f i)).2 g m) (Nat.zero_le m)
      exact ⟨Nat.lt_of_lt_of_le (ih 0 g m).1 h0, Nat.lt_of_lt_of_le (ih 0 g m).2 h0⟩
  | supL _ _ => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩
  | supH _ _ => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩

end BusyLean.Ordinal

namespace BusyLean

theorem input_lt_family55 (n : Nat) : n < family55 n :=
  Nat.lt_trans (input_lt_F55 n) (input_lt_F55 (F55 n))

/-- At every input, `F56` exceeds Contender 55's family. -/
theorem family55_lt_F56 (n : Nat) : family55 n < F56 n := by
  have hS := Ordinal.lt_jointStack prims54 (primEnv54 (family55 n) family55)
    (jointTree (family55 n)) family55
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (jointTree (family55 n))
    (family55 n)).1
  exact Nat.lt_trans (input_lt_family55 (family55 n)) (Nat.lt_of_lt_of_le (hS (family55 n)).1 h1)

theorem input_lt_F56 (n : Nat) : n < F56 n :=
  Nat.lt_trans (input_lt_family55 n) (family55_lt_F56 n)

/-- **The required comparison**: Contender 55 is strictly smaller than Contender 56. -/
theorem contender_55_lt_contender_56 : contender_55 < contender_56 :=
  Nat.lt_trans (family55_lt_F56 42) (input_lt_F56 (F56 42))

theorem contender_54_lt_contender_56 : contender_54 < contender_56 :=
  Nat.lt_trans contender_54_lt_contender_55 contender_55_lt_contender_56

end BusyLean
