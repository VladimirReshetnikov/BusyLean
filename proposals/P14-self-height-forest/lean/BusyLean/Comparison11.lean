import BusyLean.Contender11
import BusyLean.Comparison10

/-! # Contender 11: comparison theorems -/

namespace BusyLean

/-! ## Family-aware reflection -/

/-- Anything below the maximum used by `reflect11` is strictly below it. -/
theorem lt_reflect11 {fs : W.Family} {n m : Nat}
    (h : m <= BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))) :
    m < reflect11 fs n := by
  unfold reflect11
  omega

/-- Every visible child oracle value is below the family-aware reflection. -/
theorem oracle_lt_reflect11 (fs : W.Family) {i n : Nat} (hi : i <= n) :
    fs i n < reflect11 fs n :=
  lt_reflect11
    (Nat.le_trans (W.le_prefixMax (fun j => fs j n) hi)
      (BigNumber.le_maxN_left _ _))

/-- Every accepted kind-polymorphic program in the bounded enumeration is
below the family-aware reflection. -/
theorem fvalue_lt_reflect11 (fs : W.Family) {n : Nat} {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue (packFamily fs) n t < reflect11 fs n :=
  lt_reflect11
    (Nat.le_trans (W.le_maximum (Fk.fvalue (packFamily fs) n) ht)
      (BigNumber.le_maxN_right _ _))

/-- The input is below the family-aware reflection. -/
theorem input_lt_reflect11 (fs : W.Family) (n : Nat) : n < reflect11 fs n := by
  unfold reflect11
  omega

/-! ## Unary reflection towers -/

/-- Each additional unary `Fk` reflection layer is a strict increase. -/
theorem towerFk_step_lt (f : Nat -> Nat) (k n : Nat) :
    towerFk k f n < towerFk (Nat.succ k) f n := by
  change towerFk k f n < Fk.reflectFk (towerFk k f) n
  exact Fk.oracle_lt_reflectFk (towerFk k f) n

/-- At every fixed input, the tower is strictly increasing in its height. -/
theorem towerFk_strictMono (f : Nat -> Nat) (n : Nat) {a b : Nat}
    (hab : a < b) : towerFk a f n < towerFk b f n := by
  induction b generalizing a with
  | zero => omega
  | succ b ih =>
      by_cases hEq : a = b
      · subst a
        exact towerFk_step_lt f b n
      · have hlt : a < b := by omega
        exact Nat.lt_trans (ih hlt) (towerFk_step_lt f b n)

/-! ## The diagonal at a node -/

/-- Anything below either component of the diagonal maximum is strictly below
`diagonal11`. -/
theorem lt_diagonal11 {fs : W.Family} {n m : Nat}
    (h : m <= BigNumber.maxN (reflect11 fs n)
      (towerFk (reflect11 fs n + 1) (reflect11 fs) n)) :
    m < diagonal11 fs n := by
  unfold diagonal11
  omega

/-- The direct family-aware reflection is strictly below its diagonal closure. -/
theorem reflect11_lt_diagonal11 (fs : W.Family) (n : Nat) :
    reflect11 fs n < diagonal11 fs n :=
  lt_diagonal11 (BigNumber.le_maxN_left _ _)

/-- The full self-height unary tower is strictly below the diagonal closure. -/
theorem towerFk_lt_diagonal11 (fs : W.Family) (n : Nat) :
    towerFk (reflect11 fs n + 1) (reflect11 fs) n < diagonal11 fs n :=
  lt_diagonal11 (BigNumber.le_maxN_right _ _)

/-- Every tower height at most the direct reflection value is dominated. -/
theorem fixedTower_lt_diagonal11 (fs : W.Family) {k n : Nat}
    (hk : k <= reflect11 fs n) :
    towerFk k (reflect11 fs) n < diagonal11 fs n := by
  have hheight : k < reflect11 fs n + 1 := by omega
  exact Nat.lt_trans
    (towerFk_strictMono (reflect11 fs) n hheight)
    (towerFk_lt_diagonal11 fs n)

/-- In particular, every tower height at most the input is dominated. -/
theorem inputTower_lt_diagonal11 (fs : W.Family) {k n : Nat} (hkn : k <= n) :
    towerFk k (reflect11 fs) n < diagonal11 fs n :=
  fixedTower_lt_diagonal11 fs
    (Nat.le_trans hkn (Nat.le_of_lt (input_lt_reflect11 fs n)))

/-- Every visible child oracle value is below the diagonal closure. -/
theorem oracle_lt_diagonal11 (fs : W.Family) {i n : Nat} (hi : i <= n) :
    fs i n < diagonal11 fs n :=
  Nat.lt_trans (oracle_lt_reflect11 fs hi) (reflect11_lt_diagonal11 fs n)

/-- Every accepted kind-polymorphic program at a node is below the diagonal
closure at that node. -/
theorem fvalue_lt_diagonal11 (fs : W.Family) {n : Nat} {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue (packFamily fs) n t < diagonal11 fs n :=
  Nat.lt_trans (fvalue_lt_reflect11 fs ht) (reflect11_lt_diagonal11 fs n)

/-- The input is below the diagonal closure. -/
theorem input_lt_diagonal11 (fs : W.Family) (n : Nat) :
    n < diagonal11 fs n :=
  Nat.lt_trans (input_lt_reflect11 fs n) (reflect11_lt_diagonal11 fs n)

/-! ## Forest closure -/

/-- Every visible child stage is strictly below its parent stage. -/
theorem stage11_child_lt (seed : W.Family) (g : Nat -> BigNumber.WTree Nat)
    {i n : Nat} (hi : i <= n) :
    stage11 seed (g i) n < stage11 seed (.node g) n :=
  oracle_lt_diagonal11 (fun j => stage11 seed (g j)) hi

/-- The input is below every stage. -/
theorem input_lt_stage11 (seed : W.Family) (a : BigNumber.WTree Nat) (n : Nat) :
    n < stage11 seed a n := by
  cases a with
  | leaf => exact input_lt_diagonal11 seed n
  | node g => exact input_lt_diagonal11 (fun i => stage11 seed (g i)) n

/-! ## Contender 11 -/

/-- At every input, `F11` exceeds Contender 10's construction. -/
theorem family10_lt_F11 (n : Nat) : family10 n < F11 n := by
  have h1 : family10 n < stage11 (fun _ => family10) .leaf n :=
    oracle_lt_diagonal11 (fun _ => family10) (Nat.zero_le n)
  have h2 :
      stage11 (fun _ => family10)
          (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
        stage11 (fun _ => family10) (treesOfDepth 0) n :=
    stage11_child_lt _
      (fun j => defTree (nthD (BigNumber.allTerms 0) j .zero))
      (Nat.zero_le n)
  have h3 :
      stage11 (fun _ => family10) (treesOfDepth 0) n <
        stage11 (fun _ => family10) index n :=
    stage11_child_lt _ treesOfDepth (Nat.zero_le n)
  rw [first_tree_leaf] at h2
  exact Nat.lt_trans h1 (Nat.lt_trans h2 h3)

/-- **The required comparison**: Contender 10 is strictly smaller than
Contender 11. -/
theorem contender_10_lt_contender_11 : contender_10 < contender_11 :=
  Nat.lt_trans (family10_lt_F11 42)
    (input_lt_stage11 (fun _ => family10) index (F11 42))

/-- Every tree denoted by the W-language is eventually dominated by `F11`. -/
theorem defined_tree_eventually_lt11 {k : Nat} {t : BigNumber.Term}
    (ht : t ∈ BigNumber.allTerms k) :
    ∃ N, ∀ n, N <= n ->
      stage11 (fun _ => family10) (defTree t) n < F11 n := by
  obtain ⟨i, hi⟩ := exists_nthD_of_mem (d := BigNumber.Term.zero) ht
  refine ⟨k + i, fun n hn => ?_⟩
  rw [← hi]
  exact Nat.lt_trans
    (stage11_child_lt _
      (fun j => defTree (nthD (BigNumber.allTerms k) j .zero)) (by omega))
    (stage11_child_lt _ treesOfDepth (by omega))

/-- Transitive comparison with Contender 9. -/
theorem contender_9_lt_contender_11 : contender_9 < contender_11 :=
  Nat.lt_trans contender_9_lt_contender_10 contender_10_lt_contender_11

/-- Transitive comparison with Contender 8. -/
theorem contender_8_lt_contender_11 : contender_8 < contender_11 :=
  Nat.lt_trans contender_8_lt_contender_10 contender_10_lt_contender_11

end BusyLean
