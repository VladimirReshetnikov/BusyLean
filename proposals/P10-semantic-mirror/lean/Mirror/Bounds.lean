import Mirror.Enumeration
import Mirror.Semantics

namespace BusyLean.Mirror

open BigNumber (Term)
open BusyLean.W (Family prefixMax)

private theorem left_le_max : ∀ a b : Nat, a ≤ BigNumber.maxN a b
  | 0, b => Nat.zero_le b
  | a + 1, 0 => Nat.le_refl _
  | a + 1, b + 1 => Nat.succ_le_succ (left_le_max a b)

private theorem right_le_max : ∀ a b : Nat, b ≤ BigNumber.maxN a b
  | 0, b => Nat.le_refl b
  | a + 1, 0 => Nat.zero_le _
  | a + 1, b + 1 => Nat.succ_le_succ (right_le_max a b)

private theorem le_prefix (g : Nat → Nat) :
    ∀ {i k : Nat}, i ≤ k → g i ≤ prefixMax g k
  | _, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | i, k + 1, h => by
      cases Nat.lt_or_eq_of_le h with
      | inl hlt =>
          exact Nat.le_trans (le_prefix g (Nat.le_of_lt_succ hlt))
            (left_le_max _ _)
      | inr heq => rw [heq]; exact right_le_max _ _

private theorem le_maximum {A : Type} (f : A → Nat) {x : A} :
    ∀ {xs : List A}, x ∈ xs → f x ≤ BigNumber.maximum f xs
  | _ :: _, .head _ => left_le_max _ _
  | y :: _, .tail _ h => Nat.le_trans (le_maximum f h) (right_le_max (f y) _)

private theorem lt_offset {x m n : Nat} (h : x ≤ m) : x < n + 1 + m := by
  omega

theorem closed_program_lt_joinReflect (ms : Nat → Model) (fs : Family)
    {i n : Nat} {t : Term} (hi : i ≤ n)
    (ht : t ∈ BigNumber.allTerms (budget n)) :
    score (ms i) zeroFamily n t < joinReflect ms fs n := by
  have h1 : score (ms i) zeroFamily n t ≤ programMax (ms i) zeroFamily n :=
    le_maximum _ ht
  have h2 : programMax (ms i) zeroFamily n ≤ libraryBound (ms i) fs n :=
    left_le_max _ _
  have h3 := le_prefix (fun j => libraryBound (ms j) fs n) hi
  have h4 := right_le_max (BusyLean.W.reflect fs n)
    (prefixMax (fun j => libraryBound (ms j) fs n) n)
  exact lt_offset (Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4)))

theorem relative_program_lt_joinReflect (ms : Nat → Model) (fs : Family)
    {i n : Nat} {t : Term} (hi : i ≤ n)
    (ht : t ∈ BigNumber.allTerms (budget n)) :
    score (ms i) fs n t < joinReflect ms fs n := by
  have h1 : score (ms i) fs n t ≤ programMax (ms i) fs n :=
    le_maximum _ ht
  have h2 : programMax (ms i) fs n ≤ libraryBound (ms i) fs n :=
    right_le_max _ _
  have h3 := le_prefix (fun j => libraryBound (ms j) fs n) hi
  have h4 := right_le_max (BusyLean.W.reflect fs n)
    (prefixMax (fun j => libraryBound (ms j) fs n) n)
  exact lt_offset (Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4)))

theorem boost_number_lt_joinReflect (ms : Nat → Model) (fs : Family)
    {i n : Nat} (hi : i ≤ n) :
    boost (number (ms i) n) < joinReflect ms fs n := by
  have h := closed_program_lt_joinReflect ms fs hi (boostProgram_mem n)
  rw [score_boostProgram] at h
  exact h

/-- Applies at the root of any measured join model, whatever its generated index. -/
theorem boost_number_lt_join (ms : Nat → Model) {i n : Nat} (hi : i ≤ n) :
    boost (number (ms i) n) < number (join ms) n :=
  boost_number_lt_joinReflect ms
    (fun k => walk (join ms).reflection BusyLean.p5Family
      (.node (fun j => (join ms).trees k j))) hi

theorem program_lt_join (ms : Nat → Model) {i n : Nat} {t : Term}
    (hi : i ≤ n) (ht : termRank t ≤ budget n) :
    score (ms i) zeroFamily n t < number (join ms) n :=
  closed_program_lt_joinReflect ms
    (fun k => walk (join ms).reflection BusyLean.p5Family
      (.node (fun j => (join ms).trees k j))) hi
    (mem_allTerms_of_rank t ht)

/-- The zero branch of the bootstrap schedule is the exact entire old model. -/
theorem boost_number_lt_bootstrap (m : Model) (n : Nat) :
    boost (number m n) < number (bootstrap m) n :=
  boost_number_lt_join
    (fun i => foldModels m
      (match i with | 0 => .leaf | k + 1 => .node (fun j => m.trees k j)))
    (i := 0) (n := n) (Nat.zero_le n)

theorem program_lt_bootstrap (m : Model) {n : Nat} {t : Term}
    (ht : termRank t ≤ budget n) :
    score m zeroFamily n t < number (bootstrap m) n :=
  program_lt_join
    (fun i => foldModels m
      (match i with | 0 => .leaf | k + 1 => .node (fun j => m.trees k j)))
    (i := 0) (n := n) (Nat.zero_le n) ht

/-- Eventual domination of every fixed program in every fixed child library. -/
theorem eventually_dominates_child (ms : Nat → Model) (i : Nat) (t : Term) :
    ∀ n, Nat.max i (termRank t) ≤ n →
      score (ms i) zeroFamily n t < number (join ms) n := by
  intro n hn
  apply program_lt_join ms
  · exact Nat.le_trans (Nat.le_max_left _ _) hn
  · have ht := Nat.le_trans (Nat.le_max_right _ _) hn
    unfold budget
    omega

theorem no_program_for_join (ms : Nat → Model) (i : Nat) (t : Term) :
    ¬ (∀ n, score (ms i) zeroFamily n t = number (join ms) n) := by
  intro h
  let n := Nat.max i (termRank t)
  have hs := eventually_dominates_child ms i t n (Nat.le_refl n)
  rw [h n] at hs
  exact Nat.lt_irrefl _ hs

theorem no_program_for_bootstrap (m : Model) (t : Term) :
    ¬ (∀ n, score m zeroFamily n t = number (bootstrap m) n) := by
  intro h
  have hs := program_lt_bootstrap m (n := termRank t)
    (t := t) (by unfold budget; omega)
  rw [h (termRank t)] at hs
  exact Nat.lt_irrefl _ hs

/-- Exact semantic retention of a tree program in every selected child library. -/
theorem tree_slot (ms : Nat → Model) (k i : Nat) (t : Term)
    (h : BusyLean.nthD (BigNumber.allTerms k) i .zero = t) :
    (join ms).trees k i = .node (fun j => treeValue (ms j) k t) := by
  change joinTrees ms k i = _
  unfold joinTrees
  rw [h]

end BusyLean.Mirror
