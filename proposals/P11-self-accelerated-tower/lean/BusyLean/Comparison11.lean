import BusyLean.Contender11
import BusyLean.Comparison10

/-! # Contender 11: comparison and structural-margin theorems -/

namespace BusyLean

/-! ## A single family-reflection step -/

theorem lt_reflect11 {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))) :
    m < reflect11 fs n := by
  unfold reflect11
  omega

/-- Every visible oracle-family value is strictly below the reflection step. -/
theorem oracle_lt_reflect11 (fs : W.Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflect11 fs n :=
  lt_reflect11 (Nat.le_trans (W.le_prefixMax (fun j => fs j n) hi)
    (BigNumber.le_maxN_left _ _))

/-- Every enumerated, accepted kind-polymorphic program is strictly below the
reflection step. -/
theorem fvalue_lt_reflect11 (fs : W.Family) {n : Nat} {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue (packFamily fs) n t < reflect11 fs n :=
  lt_reflect11 (Nat.le_trans (W.le_maximum _ ht)
    (BigNumber.le_maxN_right _ _))

/-- The numerical input itself is strictly below every reflection step. -/
theorem input_lt_reflect11 (fs : W.Family) (n : Nat) :
    n < reflect11 fs n := by
  unfold reflect11
  omega

/-! ## Forest reflection -/

/-- Every visible child stage is strictly below its parent stage. -/
theorem stage11_child_lt (seed : W.Family)
    (g : Nat → BigNumber.WTree Nat) {i n : Nat} (hi : i ≤ n) :
    stage11 seed (g i) n < stage11 seed (.node g) n :=
  oracle_lt_reflect11 (fun j => stage11 seed (g j)) hi

/-- Forest reflection strictly exceeds its numerical input at every tree. -/
theorem input_lt_stage11 (seed : W.Family)
    (a : BigNumber.WTree Nat) (n : Nat) :
    n < stage11 seed a n := by
  cases a with
  | leaf => exact input_lt_reflect11 seed n
  | node g => exact input_lt_reflect11 _ n

/-- One full round strictly exceeds its seed pointwise.

The proof is by explicit inclusion, not a false monotonicity principle: the
constant seed occurs at the leaf, that leaf occurs in `treesOfDepth 0`, and
`treesOfDepth 0` occurs in `index`. -/
theorem seed_lt_round11 (f : Nat → Nat) (n : Nat) :
    f n < round11 f n := by
  have h₁ : f n < stage11 (fun _ => f) .leaf n :=
    oracle_lt_reflect11 (fun _ => f) (Nat.zero_le n)
  have h₂ :
      stage11 (fun _ => f)
        (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
      stage11 (fun _ => f) (treesOfDepth 0) n :=
    stage11_child_lt _
      (fun j => defTree (nthD (BigNumber.allTerms 0) j .zero))
      (Nat.zero_le n)
  have h₃ :
      stage11 (fun _ => f) (treesOfDepth 0) n <
      stage11 (fun _ => f) index n :=
    stage11_child_lt _ treesOfDepth (Nat.zero_le n)
  rw [first_tree_leaf] at h₂
  exact Nat.lt_trans h₁ (Nat.lt_trans h₂ h₃)

/-- One full round also strictly exceeds the input at which it is evaluated. -/
theorem input_lt_round11 (f : Nat → Nat) (n : Nat) :
    n < round11 f n :=
  input_lt_stage11 (fun _ => f) index n

/-- Every W-tree denoted by an enumerated W-language program is eventually
strictly below a full round with the same seed. -/
theorem defined_tree_eventually_lt11 {f : Nat → Nat} {k : Nat}
    {t : BigNumber.Term} (ht : t ∈ BigNumber.allTerms k) :
    ∃ N, ∀ n, N ≤ n →
      stage11 (fun _ => f) (defTree t) n < round11 f n := by
  obtain ⟨i, hi⟩ := exists_nthD_of_mem (d := BigNumber.Term.zero) ht
  refine ⟨k + i, fun n hn => ?_⟩
  rw [← hi]
  exact Nat.lt_trans
    (stage11_child_lt _
      (fun j => defTree (nthD (BigNumber.allTerms k) j .zero))
      (by omega))
    (stage11_child_lt _ treesOfDepth (by omega))

/-- Every accepted kind-polymorphic program at the current budget, run against
the family of child stages visible at the root of `index`, is below the round. -/
theorem fvalue_lt_round11 (f : Nat → Nat) {n : Nat} {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue
      (packFamily (fun i => stage11 (fun _ => f) (treesOfDepth i))) n t <
      round11 f n :=
  fvalue_lt_reflect11 _ ht

/-! ## The self-accelerated tower and the final diagonal -/

/-- Every successor level of the tower strictly exceeds the preceding level. -/
theorem tower11_step_lt (k n : Nat) :
    tower11 k n < tower11 (k + 1) n := by
  change tower11 k n < round11 (tower11 k) (tower11 k n)
  exact input_lt_round11 _ _

/-- Every positive tower level strictly exceeds the base family. -/
theorem family10_lt_tower11_succ : ∀ k n,
    family10 n < tower11 (k + 1) n
  | 0, n => tower11_step_lt 0 n
  | k + 1, n =>
      Nat.lt_trans (family10_lt_tower11_succ k n)
        (tower11_step_lt (k + 1) n)

/-- Contender 10's family strictly exceeds its input. -/
theorem input_lt_family10 (n : Nat) : n < family10 n := by
  unfold family10
  exact Nat.lt_trans
    (Fk.input_lt_reflectFk family9 n)
    (Fk.input_lt_reflectFk family9 (F10 n))

/-- The diagonal family strictly exceeds Contender 10's whole construction at
every input. -/
theorem family10_lt_F11 (n : Nat) : family10 n < F11 n := by
  have h₁ : family10 n < family10 (family10 n) :=
    input_lt_family10 (family10 n)
  have h₂ : family10 (family10 n) <
      tower11 (family10 n + 1) (family10 n) :=
    family10_lt_tower11_succ (family10 n) (family10 n)
  exact Nat.lt_trans h₁ h₂

/-- The final diagonal strictly exceeds its own input. -/
theorem input_lt_F11 (n : Nat) : n < F11 n :=
  Nat.lt_trans (input_lt_family10 n) (family10_lt_F11 n)

/-- **The required comparison:** Contender 10 is strictly smaller than
Contender 11. -/
theorem contender_10_lt_contender_11 : contender_10 < contender_11 := by
  have h₁ : family10 42 < F11 42 := family10_lt_F11 42
  have h₂ : F11 42 < F11 (F11 42) := input_lt_F11 (F11 42)
  simpa [family10, contender_10, contender_11] using Nat.lt_trans h₁ h₂

/-- The previous two accepted contenders are also strictly below Contender 11. -/
theorem contender_9_lt_contender_11 : contender_9 < contender_11 :=
  Nat.lt_trans contender_9_lt_contender_10 contender_10_lt_contender_11

end BusyLean
