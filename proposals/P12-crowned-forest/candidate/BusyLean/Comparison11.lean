import BusyLean.Contender11
import BusyLean.Comparison10

/-!
# Contender 11: comparison and structural theorems

The required result is `contender_10_lt_contender_11`.  The remaining theorems
make the margin inspectable: every visible child and every accepted
kind-polymorphic program is below its enclosing reflection node; consecutive
crown levels are strictly increasing; every W-language-defined tree is
eventually below `F11`; and the root reflects all depth-bounded programs
relative to the preceding crown level.
-/

namespace BusyLean

/-! ## One reflection step -/

theorem lt_reflect11 {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))) :
    m < reflect11 fs n := by
  show m < n + 1 + _
  have hM : ∀ M : Nat, M + 1 ≤ n + 1 + M := fun M => by
    rw [Nat.add_comm M 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) M
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hM _))

/-- Every child visible at input `n` is strictly below the enclosing node. -/
theorem oracle_lt_reflect11 (fs : W.Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflect11 fs n :=
  lt_reflect11 (Nat.le_trans (W.le_prefixMax (fun j => fs j n) hi)
    (BigNumber.le_maxN_left _ _))

/-- Every accepted kind-polymorphic program in the finite syntax list is below
its enclosing node. -/
theorem fvalue_lt_reflect11 (fs : W.Family) {n : Nat} {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue (packFamily fs) n t < reflect11 fs n :=
  lt_reflect11 (Nat.le_trans (W.le_maximum _ ht) (BigNumber.le_maxN_right _ _))

/-- The numerical input itself is strictly below every reflection node. -/
theorem input_lt_reflect11 (fs : W.Family) (n : Nat) : n < reflect11 fs n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

/-! ## Forest and crown structure -/

/-- A visible child stage is strictly below its parent stage. -/
theorem stage11_child_lt (seed : W.Family) (g : Nat → BigNumber.WTree Nat)
    {i n : Nat} (hi : i ≤ n) :
    stage11 seed (g i) n < stage11 seed (.node g) n :=
  oracle_lt_reflect11 (fun j => stage11 seed (g j)) hi

/-- Every stage strictly exceeds its numerical input. -/
theorem input_lt_stage11 (seed : W.Family) (a : BigNumber.WTree Nat) (n : Nat) :
    n < stage11 seed a n := by
  cases a with
  | leaf => exact input_lt_reflect11 seed n
  | node g => exact input_lt_reflect11 _ n

/-- The defining equation for one more crown level. -/
theorem crown11_succ (k : Nat) (a : BigNumber.WTree Nat) :
    crown11 (k + 1) a = .node (fun _ => crown11 k a) := rfl

/-- Consecutive crown levels are strictly increasing at every input. -/
theorem stage11_crown_step_lt (seed : W.Family) (a : BigNumber.WTree Nat)
    (k n : Nat) :
    stage11 seed (crown11 k a) n < stage11 seed (crown11 (k + 1) a) n := by
  rw [crown11_succ]
  exact stage11_child_lt seed (fun _ => crown11 k a) (Nat.zero_le n)

/-- Any positive crown is strictly above its base. -/
theorem stage11_lt_crown11 (seed : W.Family) (a : BigNumber.WTree Nat)
    (k n : Nat) :
    stage11 seed a n < stage11 seed (crown11 (k + 1) a) n := by
  induction k with
  | zero => simpa using stage11_crown_step_lt seed a 0 n
  | succ k ih =>
      exact Nat.lt_trans ih (stage11_crown_step_lt seed a (k + 1) n)

/-! ## The final family -/

/-- Before adding the crown, the self-generated index already dominates the
previous construction at every input. -/
theorem family10_lt_stage11_index (n : Nat) :
    family10 n < stage11 (fun _ => family10) index n := by
  have h1 : family10 n < stage11 (fun _ => family10) .leaf n :=
    oracle_lt_reflect11 (fun _ => family10) (Nat.zero_le n)
  have h2 :
      stage11 (fun _ => family10)
          (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
        stage11 (fun _ => family10) (treesOfDepth 0) n :=
    stage11_child_lt _ (fun j => defTree (nthD (BigNumber.allTerms 0) j .zero))
      (Nat.zero_le n)
  have h3 :
      stage11 (fun _ => family10) (treesOfDepth 0) n <
        stage11 (fun _ => family10) index n :=
    stage11_child_lt _ treesOfDepth (Nat.zero_le n)
  rw [first_tree_leaf] at h2
  exact Nat.lt_trans h1 (Nat.lt_trans h2 h3)

/-- The input-diagonal crown strictly raises the self-generated index. -/
theorem stage11_index_lt_F11 (n : Nat) :
    stage11 (fun _ => family10) index n < F11 n := by
  unfold F11
  exact stage11_lt_crown11 _ _ n n

/-- At every input, `F11` strictly exceeds Contender 10's whole family. -/
theorem family10_lt_F11 (n : Nat) : family10 n < F11 n :=
  Nat.lt_trans (family10_lt_stage11_index n) (stage11_index_lt_F11 n)

/-- Every W-language-defined tree is eventually dominated by the new family. -/
theorem defined_tree_lt_F11 {k i n : Nat} (hk : k ≤ n) (hi : i ≤ n) :
    stage11 (fun _ => family10)
        (defTree (nthD (BigNumber.allTerms k) i .zero)) n < F11 n :=
  Nat.lt_trans
    (stage11_child_lt _
      (fun j => defTree (nthD (BigNumber.allTerms k) j .zero)) hi)
    (Nat.lt_trans (stage11_child_lt _ treesOfDepth hk)
      (stage11_index_lt_F11 n))

/-- Every individual tree denoted by an enumerated W-language program is below
`F11` from an explicit input threshold onward. -/
theorem defined_tree_eventually_lt11 {k : Nat} {t : BigNumber.Term}
    (ht : t ∈ BigNumber.allTerms k) :
    ∃ N, ∀ n, N ≤ n →
      stage11 (fun _ => family10) (defTree t) n < F11 n := by
  obtain ⟨i, hi⟩ := exists_nthD_of_mem (d := BigNumber.Term.zero) ht
  refine ⟨k + i, fun n hn => ?_⟩
  rw [← hi]
  exact defined_tree_lt_F11
    (Nat.le_trans (Nat.le_add_right k i) hn)
    (Nat.le_trans (Nat.le_add_left i k) hn)

/-- At input `n`, the root of `F11 n` reflects every accepted program of depth
at most `n`, relative to the entire preceding crown level. -/
theorem root_program_lt_F11 {n : Nat} {t : Fk.CTm} (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue
        (packFamily (fun _ =>
          stage11 (fun _ => family10) (crown11 n index))) n t < F11 n := by
  unfold F11
  change Fk.fvalue
      (packFamily (fun _ =>
        stage11 (fun _ => family10) (crown11 n index))) n t <
    reflect11 (fun _ =>
      stage11 (fun _ => family10) (crown11 n index)) n
  exact fvalue_lt_reflect11 _ ht

/-- **Required comparison:** Contender 10 is strictly smaller than
Contender 11.  No numerical normalization is involved. -/
theorem contender_10_lt_contender_11 : contender_10 < contender_11 :=
  Nat.lt_trans (family10_lt_F11 42)
    (input_lt_stage11 _ (crown11 (F11 42 + 1) index) (F11 42))

/-- The previous comparisons compose transitively. -/
theorem contender_9_lt_contender_11 : contender_9 < contender_11 :=
  Nat.lt_trans contender_9_lt_contender_10 contender_10_lt_contender_11

end BusyLean
