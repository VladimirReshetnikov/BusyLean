import BigNumber.CandidateDefs
import BigNumber.Base
import BigNumber.Amplifier

namespace BigNumber

theorem base_weak (n : Nat) : n ≤ base n := Nat.le_of_lt (base_inflationary n)

theorem base_strict (n : Nat) : n + 1 ≤ base n := base_inflationary n

theorem contender_5_lt_seedScore :
    Baseline.contender_5 < Amplifier.seedScore base :=
  Nat.lt_of_lt_of_le contender_5_lt_base64
    (Amplifier.base_le_fast base base_weak (Amplifier.higherSeed 64) 64)

/-- The strict comparison required by the adapted contest. -/
theorem contender_5_lt_contender_6 : Baseline.contender_5 < contender_6 :=
  Nat.lt_of_lt_of_le contender_5_lt_base64
    (Amplifier.base_le_candidate base base_weak)

/-- Keep arithmetic symbolic before substituting the enormous constants. -/
theorem exponential_transfer (c s v : Nat) (hc : c < s)
    (hv : 65 ^ s * (s + 1) ≤ v + 1) :
    65 ^ (c + 1) * (c + 2) ≤ v + 1 := by
  have hs : c + 1 ≤ s := hc
  exact Nat.le_trans
    (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hs)
      (Nat.add_le_add_right hs 1))
    hv

/-- A quantitative lower bound, expressed directly in terms of the incumbent. -/
theorem contender_6_exponential_bound :
    65 ^ (Baseline.contender_5 + 1) * (Baseline.contender_5 + 2) ≤
      Amplifier.candidate base + 1 :=
  exponential_transfer Baseline.contender_5 (Amplifier.seedScore base)
    (Amplifier.candidate base) contender_5_lt_seedScore
    (Amplifier.candidate_bound base base_strict)

theorem tower_transfer (b : Nat → Nat) (hb : ∀ n, n + 1 ≤ b n)
    (c : Nat) (hc : c < Amplifier.seedScore b) :
    Amplifier.towerFeedback (c + 1) (c + 1) ≤ Amplifier.candidate b :=
  Amplifier.candidate_tower_from b hb (c + 1) hc

/-- A tower is built, then its value becomes the next tower height.
The process repeats more times than the incumbent's value.
-/
theorem contender_6_tower_bound :
    Amplifier.towerFeedback (Baseline.contender_5 + 1)
      (Baseline.contender_5 + 1) ≤ contender_6 :=
  tower_transfer base base_strict Baseline.contender_5 contender_5_lt_seedScore

theorem contender_6_seed_tower_bound :
    Amplifier.towerFeedback (Amplifier.seedScore base)
      (Amplifier.seedScore base) ≤ contender_6 :=
  Amplifier.candidate_tower base base_strict

end BigNumber
