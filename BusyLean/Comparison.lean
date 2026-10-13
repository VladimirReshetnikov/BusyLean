import BusyLean.Contender6
import BusyLean.ReflectionFacts
import BusyLean.PortAgreement

/-! # Contender 6: comparison theorems

The required theorem is `contender_5_lt_contender_6`. The others record the
margin over proposal P5 and the structural strength of the construction.
-/

namespace BusyLean

open BigNumber (Term WTree)
open BusyLean.W

/-! ## Comparisons -/

/-- The first visible defined tree is a leaf: depth-0 enumeration is empty. -/
theorem first_tree_leaf : defTree (nthD (BigNumber.allTerms 0) 0 .zero) = .leaf := rfl

/-- At every input, the final family exceeds P5's family. -/
theorem p5Family_lt_finalFamily (n : Nat) : p5Family 0 n < finalFamily n := by
  have h1 : p5Family 0 n < stage p5Family .leaf n := seed_lt_stage_leaf p5Family (Nat.zero_le n)
  have h2 : stage p5Family (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
      stage p5Family (treesOfDepth 0) n :=
    stage_child_lt p5Family _ (Nat.zero_le n)
  have h3 : stage p5Family (treesOfDepth 0) n < stage p5Family index n :=
    stage_child_lt p5Family treesOfDepth (Nat.zero_le n)
  rw [first_tree_leaf] at h2
  exact Nat.lt_trans h1 (Nat.lt_trans h2 h3)

/-- Contender 6 exceeds proposal P5's number. -/
theorem p5_lt_contender_6 : BigNumber.contender_6 < contender_6 :=
  p5Family_lt_finalFamily 42

/-- **The required comparison**: Contender 5 (the exact port of `Contender.v`)
is strictly smaller than Contender 6. -/
theorem contender_5_lt_contender_6 : contender_5 < contender_6 := by
  rw [PortAgreement.contender_5_eq_p5]
  exact Nat.lt_trans BigNumber.contender_5_lt_contender_6 p5_lt_contender_6

/-! ## Structural margins -/

/-- Every visible defined tree is strictly dominated by the index. -/
theorem defined_tree_lt_finalFamily {k i n : Nat} (hk : k ≤ n) (hi : i ≤ n) :
    stage p5Family (defTree (nthD (BigNumber.allTerms k) i .zero)) n < finalFamily n :=
  Nat.lt_trans
    (stage_child_lt p5Family (fun j => defTree (nthD (BigNumber.allTerms k) j .zero)) hi)
    (stage_child_lt p5Family treesOfDepth hk)

theorem exists_nthD_of_mem {α : Type} {x d : α} :
    ∀ {l : List α}, x ∈ l → ∃ i, nthD l i d = x
  | _ :: _, .head _ => ⟨0, rfl⟩
  | _ :: _, .tail _ h => match exists_nthD_of_mem h with
    | ⟨i, hi⟩ => ⟨i + 1, hi⟩

/-- **Every tree the W-language defines is eventually dominated.** For every
enumerated program `t`, the hierarchy along the tree `t` denotes is strictly
below the final family from some input on. -/
theorem defined_tree_eventually_lt {k : Nat} {t : Term} (ht : t ∈ BigNumber.allTerms k) :
    ∃ N, ∀ n, N ≤ n → stage p5Family (defTree t) n < finalFamily n := by
  obtain ⟨i, hi⟩ := exists_nthD_of_mem (d := Term.zero) ht
  refine ⟨k + i, fun n hn => ?_⟩
  rw [← hi]
  exact defined_tree_lt_finalFamily (Nat.le_trans (Nat.le_add_right k i) hn)
    (Nat.le_trans (Nat.le_add_left i k) hn)

/-- Every program of depth `≤ n`, run with the final oracle family, is
exceeded: no fixed program of the relativized language reaches the final
family's growth at large inputs. -/
theorem program_lt_finalFamily {n : Nat} {t : Term} (ht : t ∈ BigNumber.allTerms n) :
    evalWith (fun i => stage p5Family (treesOfDepth i)) t < finalFamily n :=
  evalWith_lt_reflect _ ht

end BusyLean
