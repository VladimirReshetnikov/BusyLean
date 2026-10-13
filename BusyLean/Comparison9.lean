import BusyLean.Contender9
import BusyLean.Comparison8

/-! # Contender 9: comparison theorems -/

namespace BusyLean

/-! ## The pairing code is decoded correctly -/

theorem v2_odd (m : Nat) : v2 (2 * m + 1) = 0 := by
  rw [v2, dite_eq_right (by omega)]

theorem v2_double {X : Nat} (hX : 0 < X) : v2 (2 * X) = v2 X + 1 := by
  rw [v2, dite_eq_left ⟨by omega, by omega⟩]
  congr 2
  omega

theorem v2_code (m : Nat) : ∀ i, v2 (2 ^ i * (2 * m + 1)) = i
  | 0 => by rw [Nat.pow_zero, Nat.one_mul]; exact v2_odd m
  | i + 1 => by
      have hpos : 0 < 2 ^ i * (2 * m + 1) := Nat.mul_pos (Nat.two_pow_pos i) (by omega)
      have e : 2 ^ (i + 1) * (2 * m + 1) = 2 * (2 ^ i * (2 * m + 1)) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]
      rw [e, v2_double hpos, v2_code m i]

/-- `unpair2` inverts the code `2^i · (2m+1)`, which Fω programs can compute. -/
theorem unpair2_code (i m : Nat) : unpair2 (2 ^ i * (2 * m + 1)) = (i, m) := by
  unfold unpair2
  simp only [v2_code]
  rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos i)]
  congr 1
  omega

theorem packFamily_code (fs : W.Family) (i m : Nat) :
    packFamily fs (2 ^ i * (2 * m + 1)) = fs i m := by
  unfold packFamily
  rw [unpair2_code]

/-! ## Reflection inequalities -/

theorem lt_reflect9 {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fw.fvalue (packFamily fs) n) (Fw.ctmsUpTo n))) :
    m < reflect9 fs n := by
  unfold reflect9
  omega

theorem oracle_lt_reflect9 (fs : W.Family) {i n : Nat} (hi : i ≤ n) : fs i n < reflect9 fs n :=
  lt_reflect9 (Nat.le_trans (W.le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

theorem fvalue_lt_reflect9 (fs : W.Family) {n : Nat} {t : Fw.CTm} (ht : t ∈ Fw.ctmsUpTo n) :
    Fw.fvalue (packFamily fs) n t < reflect9 fs n :=
  lt_reflect9 (Nat.le_trans (W.le_maximum _ ht) (BigNumber.le_maxN_right _ _))

theorem input_lt_reflect9 (fs : W.Family) (n : Nat) : n < reflect9 fs n := by
  unfold reflect9
  omega

theorem stage9_child_lt (seed : W.Family) (g : Nat → BigNumber.WTree Nat) {i n : Nat}
    (hi : i ≤ n) : stage9 seed (g i) n < stage9 seed (.node g) n :=
  oracle_lt_reflect9 (fun j => stage9 seed (g j)) hi

theorem input_lt_stage9 (seed : W.Family) (a : BigNumber.WTree Nat) (n : Nat) :
    n < stage9 seed a n := by
  cases a with
  | leaf => exact input_lt_reflect9 seed n
  | node g => exact input_lt_reflect9 _ n

/-! ## Contender 9 -/

/-- At every input, `F9` exceeds Contender 8's family. -/
theorem family8_lt_F9 (n : Nat) : family8 n < F9 n := by
  have h₁ : family8 n < stage9 (fun _ => family8) .leaf n :=
    oracle_lt_reflect9 (fun _ => family8) (Nat.zero_le n)
  have h₂ : stage9 (fun _ => family8) (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
      stage9 (fun _ => family8) (treesOfDepth 0) n :=
    stage9_child_lt _ (fun j => defTree (nthD (BigNumber.allTerms 0) j .zero)) (Nat.zero_le n)
  have h₃ : stage9 (fun _ => family8) (treesOfDepth 0) n < stage9 (fun _ => family8) index n :=
    stage9_child_lt _ treesOfDepth (Nat.zero_le n)
  rw [first_tree_leaf] at h₂
  exact Nat.lt_trans h₁ (Nat.lt_trans h₂ h₃)

/-- **The required comparison**: Contender 8 is strictly smaller than Contender 9. -/
theorem contender_8_lt_contender_9 : contender_8 < contender_9 :=
  Nat.lt_trans (family8_lt_F9 42) (input_lt_stage9 _ index (F9 42))

/-- Every tree the W-language defines is eventually dominated, now with Fω
reflection at every node. -/
theorem defined_tree_eventually_lt9 {k : Nat} {t : BigNumber.Term}
    (ht : t ∈ BigNumber.allTerms k) :
    ∃ N, ∀ n, N ≤ n → stage9 (fun _ => family8) (defTree t) n < F9 n := by
  obtain ⟨i, hi⟩ := exists_nthD_of_mem (d := BigNumber.Term.zero) ht
  refine ⟨k + i, fun n hn => ?_⟩
  rw [← hi]
  exact Nat.lt_trans
    (stage9_child_lt _ (fun j => defTree (nthD (BigNumber.allTerms k) j .zero)) (by omega))
    (stage9_child_lt _ treesOfDepth (by omega))

theorem contender_7_lt_contender_9 : contender_7 < contender_9 :=
  Nat.lt_trans contender_7_lt_contender_8 contender_8_lt_contender_9

end BusyLean
