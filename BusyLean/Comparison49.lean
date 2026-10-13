import BusyLean.Contender49
import BusyLean.Comparison48

/-! # Contender 49: comparison theorems -/

namespace BusyLean

theorem le_treeReflect_of {g : Nat → Nat} {T : Ordinal.CTree} {m x : Nat}
    (h : x ≤ BigNumber.maxN (g m) (BigNumber.maximum (FT2.natValue ⟨g, T⟩) (FT2.ctmsUpTo m))) :
    x < treeReflect g T m := by
  show x < m + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ m + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 m) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_treeReflect (g : Nat → Nat) (T : Ordinal.CTree) (m : Nat) :
    g m < treeReflect g T m :=
  le_treeReflect_of (BigNumber.le_maxN_left _ _)

theorem input_lt_treeReflect (g : Nat → Nat) (T : Ordinal.CTree) (m : Nat) :
    m < treeReflect g T m := by
  show m < m + 1 + _
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_add_right _ _)

/-- Every FT2 program of depth `<= m` reading the tree is below the reflection. -/
theorem natValue_lt_treeReflect (g : Nat → Nat) (T : Ordinal.CTree) {m : Nat} {t : FT2.CTm}
    (ht : t ∈ FT2.ctmsUpTo m) : FT2.natValue ⟨g, T⟩ t < treeReflect g T m :=
  le_treeReflect_of (Nat.le_trans (W.le_maximum _ ht) (BigNumber.le_maxN_right _ _))

theorem input_lt_family48 (n : Nat) : n < family48 n :=
  Nat.lt_trans (input_lt_F48 n) (input_lt_F48 (F48 n))

/-- At every input, `F49` exceeds Contender 48's family. -/
theorem family48_lt_F49 (n : Nat) : family48 n < F49 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_treeReflect family48
    (levelIterTree (family48 n)) x)) (levelIterTree (family48 n)) (family48 n)).1
  have h2 := oracle_lt_treeReflect family48 (levelIterTree (family48 n)) (family48 n)
  exact Nat.lt_trans (input_lt_family48 (family48 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F49 (n : Nat) : n < F49 n :=
  Nat.lt_trans (input_lt_family48 n) (family48_lt_F49 n)

/-- **The required comparison**: Contender 48 is strictly smaller than Contender 49. -/
theorem contender_48_lt_contender_49 : contender_48 < contender_49 :=
  Nat.lt_trans (family48_lt_F49 42) (input_lt_F49 (F49 42))

theorem contender_47_lt_contender_49 : contender_47 < contender_49 :=
  Nat.lt_trans contender_47_lt_contender_48 contender_48_lt_contender_49

end BusyLean
