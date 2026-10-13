import BusyLean.Contender38
import BusyLean.Comparison37

/-! # Contender 38: comparison theorems -/

namespace BusyLean.Ordinal

theorem le_iterN {h : Nat → Nat} (hh : ∀ x, x ≤ h x) : ∀ k x, x ≤ iterN h k x
  | 0, _ => Nat.le_refl _
  | k + 1, x => Nat.le_trans (hh x) (le_iterN hh k (h x))

theorem le_maxUpTo (h : Nat → Nat) : ∀ {i m : Nat}, i ≤ m → h i ≤ maxUpTo h m
  | i, 0, hi => by
      have : i = 0 := Nat.le_zero.mp hi
      subst this; exact Nat.le_refl _
  | i, m + 1, hi => by
      show h i ≤ max (maxUpTo h m) (h (m + 1))
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · exact Nat.le_trans (le_maxUpTo h (Nat.le_of_lt_succ hlt)) (Nat.le_max_left _ _)
      · have : i = m + 1 := Nat.le_antisymm hi hge
        subst this; exact Nat.le_max_right _ _

/-- The hierarchy dominates its base and its argument. -/
theorem le_hier {g : Nat → Nat} (hg : ∀ x, x ≤ g x) :
    ∀ (t : CTree) (m : Nat), g m ≤ hier g t m ∧ m ≤ hier g t m := by
  intro t
  induction t with
  | zero => intro m; exact ⟨Nat.le_refl _, hg m⟩
  | succ t ih =>
      intro m
      show g m ≤ iterN (hier g t) (m + 1) m ∧ m ≤ iterN (hier g t) (m + 1) m
      have hh : ∀ x, x ≤ hier g t x := fun x => (ih x).2
      have h1 : hier g t m ≤ iterN (hier g t) (m + 1) m := le_iterN hh m (hier g t m)
      exact ⟨Nat.le_trans (ih m).1 h1, Nat.le_trans (ih m).2 h1⟩
  | lim f ih =>
      intro m
      show g m ≤ maxUpTo (fun i => hier g (f i) m) m ∧ m ≤ maxUpTo (fun i => hier g (f i) m) m
      have h0 := le_maxUpTo (fun i => hier g (f i) m) (Nat.zero_le m)
      exact ⟨Nat.le_trans (ih 0 m).1 h0, Nat.le_trans (ih 0 m).2 h0⟩
  | supL _ _ => intro m; exact ⟨Nat.le_refl _, hg m⟩
  | supH _ _ => intro m; exact ⟨Nat.le_refl _, hg m⟩

end BusyLean.Ordinal

namespace BusyLean

theorem input_lt_family37 (n : Nat) : n < family37 n :=
  Nat.lt_trans (input_lt_F37 n) (input_lt_F37 (F37 n))

/-- At every input, `F38` exceeds Contender 37's family. -/
theorem family37_lt_F38 (n : Nat) : family37 n < F38 n :=
  Nat.lt_of_lt_of_le (input_lt_family37 (family37 n))
    (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_family37 x)) (jumpTree n) (family37 n)).1

theorem input_lt_F38 (n : Nat) : n < F38 n :=
  Nat.lt_trans (input_lt_family37 n) (family37_lt_F38 n)

/-- **The required comparison**: Contender 37 is strictly smaller than Contender 38. -/
theorem contender_37_lt_contender_38 : contender_37 < contender_38 :=
  Nat.lt_trans (family37_lt_F38 42) (input_lt_F38 (F38 42))

theorem contender_36_lt_contender_38 : contender_36 < contender_38 :=
  Nat.lt_trans contender_36_lt_contender_37 contender_37_lt_contender_38

end BusyLean
