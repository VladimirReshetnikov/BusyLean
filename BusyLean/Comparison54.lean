import BusyLean.Contender54
import BusyLean.Comparison53

/-! # Contender 54: comparison theorems -/

namespace BusyLean

theorem le_numReflect_of {N : Nat} {g : Nat → Nat} {m x : Nat}
    (h : x ≤ BigNumber.maxN (g m)
      (BigNumber.maximum id (Ordinal.PTL.natsUpTo prims54 (primEnv54 N g) m))) :
    x < numReflect N g m := by
  show x < m + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ m + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 m) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

theorem oracle_lt_numReflect (N : Nat) (g : Nat → Nat) (m : Nat) : g m < numReflect N g m :=
  le_numReflect_of (BigNumber.le_maxN_left _ _)

theorem input_lt_numReflect (N : Nat) (g : Nat → Nat) (m : Nat) : m < numReflect N g m := by
  show m < m + 1 + _
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_add_right _ _)

/-- Every closed `nat` program of size `<= m` over the primitives is below the reflection. -/
theorem program_lt_numReflect (N : Nat) (g : Nat → Nat) {m v : Nat}
    (hv : v ∈ Ordinal.PTL.natsUpTo prims54 (primEnv54 N g) m) : v < numReflect N g m :=
  le_numReflect_of (Nat.le_trans (W.le_maximum id hv) (BigNumber.le_maxN_right _ _))

theorem input_lt_family53 (n : Nat) : n < family53 n :=
  Nat.lt_trans (input_lt_F53 n) (input_lt_F53 (F53 n))

/-- At every input, `F54` exceeds Contender 53's family. -/
theorem family53_lt_F54 (n : Nat) : family53 n < F54 n := by
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (input_lt_numReflect (family53 n) family53 x))
    (stackTree (family53 n)) (family53 n)).1
  have h2 := oracle_lt_numReflect (family53 n) family53 (family53 n)
  exact Nat.lt_trans (input_lt_family53 (family53 n)) (Nat.lt_of_lt_of_le h2 h1)

theorem input_lt_F54 (n : Nat) : n < F54 n :=
  Nat.lt_trans (input_lt_family53 n) (family53_lt_F54 n)

/-- **The required comparison**: Contender 53 is strictly smaller than Contender 54. -/
theorem contender_53_lt_contender_54 : contender_53 < contender_54 :=
  Nat.lt_trans (family53_lt_F54 42) (input_lt_F54 (F54 42))

theorem contender_52_lt_contender_54 : contender_52 < contender_54 :=
  Nat.lt_trans contender_52_lt_contender_53 contender_53_lt_contender_54

end BusyLean
