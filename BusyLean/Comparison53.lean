import BusyLean.Contender53
import BusyLean.Comparison52

/-! # Contender 53: comparison theorems -/

namespace BusyLean

/-- Iterated reflection dominates its base and its argument (for an inflationary base). -/
theorem le_reflAlong (T : Ordinal.CTree) {g : Nat → Nat} (hg : ∀ x, x ≤ g x) :
    ∀ (a : Ordinal.CTree) (m : Nat), g m ≤ reflAlong T g a m ∧ m ≤ reflAlong T g a m := by
  intro a
  induction a with
  | zero => intro m; exact ⟨Nat.le_refl _, hg m⟩
  | succ a ih =>
      intro m
      have h1 := Nat.le_of_lt (Nat.lt_trans (oracle_lt_treeReflect (reflAlong T g a) T m)
        (treeReflect_lt_ladderReflect (reflAlong T g a) T m))
      exact ⟨Nat.le_trans (ih m).1 h1, Nat.le_of_lt (input_lt_ladderReflect _ T m)⟩
  | lim f ih =>
      intro m
      show g m ≤ Ordinal.maxUpTo (fun i => reflAlong T g (f i) m) m ∧
        m ≤ Ordinal.maxUpTo (fun i => reflAlong T g (f i) m) m
      have h0 := Ordinal.le_maxUpTo (fun i => reflAlong T g (f i) m) (Nat.zero_le m)
      exact ⟨Nat.le_trans (ih 0 m).1 h0, Nat.le_trans (ih 0 m).2 h0⟩
  | supL _ _ => intro m; exact ⟨Nat.le_refl _, hg m⟩
  | supH _ _ => intro m; exact ⟨Nat.le_refl _, hg m⟩

theorem input_lt_family52 (n : Nat) : n < family52 n :=
  Nat.lt_trans (input_lt_F52 n) (input_lt_F52 (F52 n))

/-- At every input, `F53` exceeds Contender 52's family. -/
theorem family52_lt_F53 (n : Nat) : family52 n < F53 n := by
  have hg : ∀ x, x ≤ family52 x := fun x => Nat.le_of_lt (input_lt_family52 x)
  have hR := le_reflAlong (stackTree (family52 n)) hg (stackTree (family52 n))
  have h1 := (Ordinal.le_hier (fun x => (hR x).2) (stackTree (family52 n)) (family52 n)).1
  exact Nat.lt_of_lt_of_le (input_lt_family52 (family52 n)) (Nat.le_trans (hR (family52 n)).1 h1)

theorem input_lt_F53 (n : Nat) : n < F53 n :=
  Nat.lt_trans (input_lt_family52 n) (family52_lt_F53 n)

/-- **The required comparison**: Contender 52 is strictly smaller than Contender 53. -/
theorem contender_52_lt_contender_53 : contender_52 < contender_53 :=
  Nat.lt_trans (family52_lt_F53 42) (input_lt_F53 (F53 42))

theorem contender_51_lt_contender_53 : contender_51 < contender_53 :=
  Nat.lt_trans contender_51_lt_contender_52 contender_52_lt_contender_53

end BusyLean
