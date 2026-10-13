import BusyLean.Contender55
import BusyLean.Comparison54

/-! # Contender 55: comparison theorems -/

namespace BusyLean.Ordinal

theorem le_numLift_of {P : List TL.Ty} {σ : TL.Env P} {g : Nat → Nat} {m x : Nat}
    (h : x ≤ BigNumber.maxN (g m)
      (BigNumber.maximum id (PTL.natsUpTo (.arr .nat .nat :: P) (g, σ) m))) :
    x < numLift P σ g m := by
  show x < m + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ m + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 m) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_numLift (P : List TL.Ty) (σ : TL.Env P) (g : Nat → Nat) (m : Nat) :
    g m < numLift P σ g m :=
  le_numLift_of (BigNumber.le_maxN_left _ _)

theorem input_lt_numLift (P : List TL.Ty) (σ : TL.Env P) (g : Nat → Nat) (m : Nat) :
    m < numLift P σ g m := by
  show m < m + 1 + _
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_add_right _ _)

/-- Every closed `nat` program over the primitives plus `g` is below the closure. -/
theorem program_lt_numLift (P : List TL.Ty) (σ : TL.Env P) (g : Nat → Nat) {m v : Nat}
    (hv : v ∈ PTL.natsUpTo (.arr .nat .nat :: P) (g, σ) m) : v < numLift P σ g m :=
  le_numLift_of (Nat.le_trans (W.le_maximum id hv) (BigNumber.le_maxN_right _ _))

/-- Every level of the stack strictly dominates its oracle and its argument. -/
theorem lt_numStack (P : List TL.Ty) (σ : TL.Env P) :
    ∀ (a : CTree) (g : Nat → Nat) (m : Nat),
      g m < numStack P σ a g m ∧ m < numStack P σ a g m := by
  intro a
  induction a with
  | zero => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩
  | succ a _ =>
      intro g m
      exact ⟨oracle_lt_numLift _ _ g m, input_lt_numLift _ _ g m⟩
  | lim f ih =>
      intro g m
      show g m < maxUpTo (fun i => numStack P σ (f i) g m) m ∧
        m < maxUpTo (fun i => numStack P σ (f i) g m) m
      have h0 := le_maxUpTo (fun i => numStack P σ (f i) g m) (Nat.zero_le m)
      exact ⟨Nat.lt_of_lt_of_le (ih 0 g m).1 h0, Nat.lt_of_lt_of_le (ih 0 g m).2 h0⟩
  | supL _ _ => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩
  | supH _ _ => intro g m; exact ⟨oracle_lt_numLift P σ g m, input_lt_numLift P σ g m⟩

end BusyLean.Ordinal

namespace BusyLean

theorem input_lt_family54 (n : Nat) : n < family54 n :=
  Nat.lt_trans (input_lt_F54 n) (input_lt_F54 (F54 n))

/-- At every input, `F55` exceeds Contender 54's family. -/
theorem family54_lt_F55 (n : Nat) : family54 n < F55 n := by
  have hS := Ordinal.lt_numStack prims54 (primEnv54 (family54 n) family54) (stackTree (family54 n))
    family54
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (stackTree (family54 n))
    (family54 n)).1
  exact Nat.lt_trans (input_lt_family54 (family54 n)) (Nat.lt_of_lt_of_le (hS (family54 n)).1 h1)

theorem input_lt_F55 (n : Nat) : n < F55 n :=
  Nat.lt_trans (input_lt_family54 n) (family54_lt_F55 n)

/-- **The required comparison**: Contender 54 is strictly smaller than Contender 55. -/
theorem contender_54_lt_contender_55 : contender_54 < contender_55 :=
  Nat.lt_trans (family54_lt_F55 42) (input_lt_F55 (F55 42))

theorem contender_53_lt_contender_55 : contender_53 < contender_55 :=
  Nat.lt_trans contender_53_lt_contender_54 contender_54_lt_contender_55

end BusyLean
