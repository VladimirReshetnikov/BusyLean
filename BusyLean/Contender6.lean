import BusyLean.Reflection
import BusyLean.PortAgreement

/-!
# Contender 6

```
contender_6 := stage p5Family index 42
```

* `stage` is forest reflection over P5's W-language (`BusyLean/Reflection.lean`).
* `index` is the join of **every tree `W ℕ` that a closed program of the
  W-language defines**: its `k`-th child joins, in enumeration order, the trees
  denoted by all programs of enumeration depth `≤ k`. The reflection hierarchy
  therefore runs along the language's *own* ordinals, rather than along an
  explicit notation system as in P1–P4.
* `p5Family` is the family of P5's proposed number (`BigNumber.iterate
  BigNumber.diagonal n n`). With it as seed, the comparison with P5 is a theorem
  (`p5_lt_contender_6`) and not only an ordinal estimate.

Informal size: with |L| ≈ ψ(Ω_ω) the W-language's ordinal, P5 is about
f_{|L|+ω²}(42), while `contender_6` is about f_{|L|·|L|}(42). See the README.

**Do not evaluate `contender_6`.**
-/

namespace BusyLean

open BigNumber (Term WTree)
open BusyLean.W

/-- The `W ℕ` tree denoted by a closed program (`leaf` if it denotes no tree;
the conversion is P5's own cast). -/
def defTree (t : Term) : WTree Nat :=
  BigNumber.castValue (.wt .nat) (BigNumber.interpret [] t).2

/-- The `i`-th list element, or a default value. -/
def nthD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, i + 1, d => nthD xs i d

/-- Join of the trees defined by all programs of enumeration depth `≤ k`. -/
def treesOfDepth (k : Nat) : WTree Nat :=
  .node fun i => defTree (nthD (BigNumber.allTerms k) i .zero)

/-- Join of all trees the W-language defines. -/
def index : WTree Nat := .node treesOfDepth

/-- The seed family: P5's proposed number, as a function of its input. -/
def p5Family : Family := fun _ n => BigNumber.iterate BigNumber.diagonal n n

/-- The reflection hierarchy along `index`. -/
def finalFamily (n : Nat) : Nat := stage p5Family index n

/-- **Contender 6.** Never evaluate it. -/
def contender_6 : Nat := finalFamily 42

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
