import BusyLean7.Selectors

/-! Exact cofinality relative to the object language, without an ordinal label. -/
namespace BusyLean7
open BigNumber (Term)

theorem exists_nthD {A : Type} {x : A} (fallback : A) :
    ∀ {xs : List A}, x ∈ xs → ∃ i, BusyLean.nthD xs i fallback = x
  | _ :: _, .head _ => ⟨0, rfl⟩
  | _ :: xs, .tail _ h => by
      obtain ⟨i, hi⟩ := exists_nthD fallback h
      exact ⟨i + 1, hi⟩

/-- Every fixed definable tree, at every fixed numerical parameter, eventually
has its entire model-ramification construction dominated by the universal one. -/
theorem ramify_index_eventually_dominates (base M : Model) (t : Term) (input : Nat) :
    ∃ N, ∀ n, N ≤ n →
      value (ramify base (treeOf M input t)) n <
        value (ramify base (modelIndex M)) n := by
  let depth := termRank t
  have ht : t ∈ BigNumber.allTerms depth := term_mem t depth (Nat.le_refl _)
  obtain ⟨position, hp⟩ := exists_nthD Term.zero ht
  let N := Nat.max 11 (Nat.max (depth + 7) (Nat.max (input + 7) (position + 7)))
  refine ⟨N, ?_⟩
  intro n hn
  have h11 : 11 ≤ n := by dsimp [N] at hn; omega
  have hd : depth + 7 ≤ n := by dsimp [N] at hn; omega
  have hm : input + 7 ≤ n := by dsimp [N] at hn; omega
  have hi : position + 7 ≤ n := by dsimp [N] at hn; omega
  let inner : Nat → Nat → Nat → Tree := fun d m i =>
    treeOf M m (BusyLean.nthD (BigNumber.allTerms d) i .zero)
  have h0 := ramify_child_lt base (inner depth input) h11 hi
  have h1 := ramify_child_lt base (fun m => BigNumber.WTree.node (inner depth m)) h11 hm
  have h2 := ramify_child_lt base
    (fun d => BigNumber.WTree.node (fun m => BigNumber.WTree.node (inner d m))) h11 hd
  have h := Nat.lt_trans h0 (Nat.lt_trans h1 h2)
  change value (ramify base (treeOf M input
      (BusyLean.nthD (BigNumber.allTerms depth) position .zero))) n <
    value (ramify base (modelIndex M)) n at h
  rw [hp] at h
  exact h

end BusyLean7
