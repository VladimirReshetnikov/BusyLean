import BusyLean.Contender7
import Mirror.Bounds
import Mirror.Growth

namespace BusyLean.Mirror

theorem boostIter_le_rounds (m : Model) (k n : Nat) :
    boostIter k (number m n) ≤ number (rounds m k) n := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_trans (boost_mono ih)
        (Nat.le_of_lt (boost_number_lt_bootstrap (rounds m k) n))

theorem number_lt_bootstrap (m : Model) (n : Nat) :
    number m n < number (bootstrap m) n :=
  Nat.lt_trans (self_lt_boost _) (boost_number_lt_bootstrap m n)

/-- Uniform quantitative comparison: the exponent count depends on the input. -/
theorem iterated_boost_lt_final (n : Nat) :
    boostIter (n + 2) (BusyLean.finalFamily n) < finalNumber n := by
  have hround := boostIter_le_rounds initialModel n n
  have hlimit := boost_number_lt_join (rounds initialModel) (i := n) (n := n)
    (Nat.le_refl n)
  have hfirst : boostIter (n + 1) (number initialModel n) < number limitModel n :=
    Nat.lt_of_le_of_lt (boost_mono hround) hlimit
  have hlast := boost_number_lt_bootstrap limitModel n
  have hfinal : boostIter (n + 2) (number initialModel n) < finalNumber n :=
    Nat.lt_of_le_of_lt (boost_mono (Nat.le_of_lt hfirst)) hlast
  rw [number_initial] at hfinal
  exact hfinal

theorem base_lt_final (n : Nat) : BusyLean.finalFamily n < finalNumber n :=
  Nat.lt_of_le_of_lt (self_le_boostIter (n + 2) (BusyLean.finalFamily n))
    (iterated_boost_lt_final n)

/-- Beyond every fixed program in every finite bootstrap-round library. -/
theorem finite_round_program_lt_final (k : Nat) (t : BigNumber.Term)
    (n : Nat) (hn : Nat.max k (termRank t) ≤ n) :
    score (rounds initialModel k) zeroFamily n t < finalNumber n :=
  Nat.lt_trans (eventually_dominates_child (rounds initialModel) k t n hn)
    (number_lt_bootstrap limitModel n)

theorem no_finite_round_program_for_final (k : Nat) (t : BigNumber.Term) :
    ¬ (∀ n, score (rounds initialModel k) zeroFamily n t = finalNumber n) := by
  intro h
  let n := Nat.max k (termRank t)
  have hs := finite_round_program_lt_final k t n (Nat.le_refl n)
  rw [h n] at hs
  exact Nat.lt_irrefl _ hs

theorem no_limit_program_for_final (t : BigNumber.Term) :
    ¬ (∀ n, score limitModel zeroFamily n t = finalNumber n) :=
  no_program_for_bootstrap limitModel t

end BusyLean.Mirror

namespace BusyLean

/-- The requested comparison, specialized only after the generic proof. -/
theorem contender_6_lt_contender_7 : contender_6 < contender_7 :=
  Mirror.base_lt_final 42

/-- Forty-four repeated self-sized exponential-tower transformations. -/
theorem contender_7_tower_margin :
    Mirror.boostIter 44 contender_6 < contender_7 :=
  Mirror.iterated_boost_lt_final 42

end BusyLean
