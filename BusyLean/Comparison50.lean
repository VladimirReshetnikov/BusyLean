import BusyLean.Contender50
import BusyLean.Comparison49

/-! # Contender 50: comparison theorems -/

namespace BusyLean

theorem le_ladderReflect_of {g : Nat → Nat} {T : Ordinal.CTree} {m x : Nat}
    (h : x ≤ BigNumber.maxN (treeReflect g T m)
      (BigNumber.maximum (FLT2.readNat g T m) (FLT2.ctmsUpTo (Ordinal.addrUpTo T m) m))) :
    x < ladderReflect g T m := by
  show x < m + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ m + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 m) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem treeReflect_lt_ladderReflect (g : Nat → Nat) (T : Ordinal.CTree) (m : Nat) :
    treeReflect g T m < ladderReflect g T m :=
  le_ladderReflect_of (BigNumber.le_maxN_left _ _)

theorem input_lt_ladderReflect (g : Nat → Nat) (T : Ordinal.CTree) (m : Nat) :
    m < ladderReflect g T m :=
  Nat.lt_trans (input_lt_treeReflect g T m) (treeReflect_lt_ladderReflect g T m)

/-- Every numeric ladder reader program of depth `<= m` is below the reflection. -/
theorem readNat_lt_ladderReflect (g : Nat → Nat) (T : Ordinal.CTree) {m : Nat}
    {p : FLT2.CTm (Ordinal.Addr T)} (hp : p ∈ FLT2.ctmsUpTo (Ordinal.addrUpTo T m) m) :
    FLT2.readNat g T m p < ladderReflect g T m :=
  le_ladderReflect_of (Nat.le_trans (W.le_maximum _ hp) (BigNumber.le_maxN_right _ _))

theorem input_lt_family49 (n : Nat) : n < family49 n :=
  Nat.lt_trans (input_lt_F49 n) (input_lt_F49 (F49 n))

/-- At every input, `F50` exceeds Contender 49's family. -/
theorem family49_lt_F50 (n : Nat) : family49 n < F50 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_ladderReflect family49
    (levelIterTree (family49 n)) x)) (levelIterTree (family49 n)) (family49 n)).1
  have h2 := Nat.lt_trans (oracle_lt_treeReflect family49 (levelIterTree (family49 n)) (family49 n))
    (treeReflect_lt_ladderReflect family49 (levelIterTree (family49 n)) (family49 n))
  exact Nat.lt_trans (input_lt_family49 (family49 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F50 (n : Nat) : n < F50 n :=
  Nat.lt_trans (input_lt_family49 n) (family49_lt_F50 n)

/-- **The required comparison**: Contender 49 is strictly smaller than Contender 50. -/
theorem contender_49_lt_contender_50 : contender_49 < contender_50 :=
  Nat.lt_trans (family49_lt_F50 42) (input_lt_F50 (F50 42))

theorem contender_48_lt_contender_50 : contender_48 < contender_50 :=
  Nat.lt_trans contender_48_lt_contender_49 contender_49_lt_contender_50

end BusyLean
