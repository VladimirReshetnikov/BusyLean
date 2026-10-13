import BusyLean.Contender11
import BusyLean.Comparison10

/-! # Contender 11: comparison theorems -/

namespace BusyLean

/-! ## Reflection inequalities -/

theorem lt_reflect11 {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))) :
    m < reflect11 fs n := by
  unfold reflect11
  omega

theorem oracle_lt_reflect11 (fs : W.Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflect11 fs n :=
  lt_reflect11 (Nat.le_trans (W.le_prefixMax (fun j => fs j n) hi)
    (BigNumber.le_maxN_left _ _))

theorem fvalue_lt_reflect11 (fs : W.Family) {n : Nat} {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue (packFamily fs) n t < reflect11 fs n :=
  lt_reflect11 (Nat.le_trans (W.le_maximum _ ht)
    (BigNumber.le_maxN_right _ _))

theorem input_lt_reflect11 (fs : W.Family) (n : Nat) :
    n < reflect11 fs n := by
  unfold reflect11
  omega

theorem stage11_child_lt (seed : W.Family)
    (g : Nat → BigNumber.WTree Nat) {i n : Nat} (hi : i ≤ n) :
    stage11 seed (g i) n < stage11 seed (.node g) n :=
  oracle_lt_reflect11 (fun j => stage11 seed (g j)) hi

theorem input_lt_stage11 (seed : W.Family)
    (a : BigNumber.WTree Nat) (n : Nat) : n < stage11 seed a n := by
  cases a with
  | leaf => exact input_lt_reflect11 seed n
  | node g => exact input_lt_reflect11 _ n

/-! ## Contender 11 -/

/-- At every input, `F11` exceeds Contender 10's entire generating family. -/
theorem family10_lt_F11 (n : Nat) : family10 n < F11 n := by
  have h₁ : family10 n < stage11 (fun _ => family10) .leaf n :=
    oracle_lt_reflect11 (fun _ => family10) (Nat.zero_le n)
  have h₂ :
      stage11 (fun _ => family10)
          (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
        stage11 (fun _ => family10) (treesOfDepth 0) n :=
    stage11_child_lt _
      (fun j => defTree (nthD (BigNumber.allTerms 0) j .zero))
      (Nat.zero_le n)
  have h₃ : stage11 (fun _ => family10) (treesOfDepth 0) n <
      stage11 (fun _ => family10) index n :=
    stage11_child_lt _ treesOfDepth (Nat.zero_le n)
  rw [first_tree_leaf] at h₂
  exact Nat.lt_trans h₁ (Nat.lt_trans h₂ h₃)

/-- **The required comparison**: Contender 10 is strictly smaller. -/
theorem contender_10_lt_contender_11 : contender_10 < contender_11 :=
  Nat.lt_trans (family10_lt_F11 42)
    (input_lt_stage11 _ index (F11 42))

/-- Every tree defined by the W-language is eventually dominated, with
kind-polymorphic reflection at every node. -/
theorem defined_tree_eventually_lt11 {k : Nat} {t : BigNumber.Term}
    (ht : t ∈ BigNumber.allTerms k) :
    ∃ N, ∀ n, N ≤ n →
      stage11 (fun _ => family10) (defTree t) n < F11 n := by
  obtain ⟨i, hi⟩ := exists_nthD_of_mem (d := BigNumber.Term.zero) ht
  refine ⟨k + i, fun n hn => ?_⟩
  rw [← hi]
  exact Nat.lt_trans
    (stage11_child_lt _
      (fun j => defTree (nthD (BigNumber.allTerms k) j .zero)) (by omega))
    (stage11_child_lt _ treesOfDepth (by omega))

/-- Every kind-polymorphic program visible at budget `n` is below `F11 n`. -/
theorem fvalue_lt_F11 {n : Nat} {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue (packFamily rootFamily11) n t < F11 n := by
  unfold F11 index rootFamily11
  exact fvalue_lt_reflect11 _ ht

/-- Every kind-polymorphic program at the final inner budget is exceeded. -/
theorem fvalue_lt_contender_11 {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo (F11 42)) :
    Fk.fvalue (packFamily rootFamily11) (F11 42) t < contender_11 :=
  fvalue_lt_F11 ht

theorem contender_9_lt_contender_11 : contender_9 < contender_11 :=
  Nat.lt_trans contender_9_lt_contender_10 contender_10_lt_contender_11

end BusyLean
