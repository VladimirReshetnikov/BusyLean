import BusyLean7.Reflection
import BusyLean7.Arithmetic

/-! Quantitative comparisons. No normalization of either contender is used. -/
namespace BusyLean7

theorem next_margin (M : Model) {n : Nat} (hn : 11 ≤ n) :
    theta (value M n) < value (next M) n := by
  simpa only [next, value] using amplified_zero_lt_value (next M) hn

theorem finite_bound (M : Model) {n : Nat} (hn : 11 ≤ n) (k : Nat) :
    iter theta k (value M n) ≤ value (finite M k) n := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt (theta_mono ih)
        (next_margin (finite M k) hn))

theorem finite_base_le (M : Model) {n : Nat} (hn : 11 ≤ n) (k : Nat) :
    value M n ≤ value (finite M k) n :=
  Nat.le_trans (le_iter theta (fun x => Nat.le_of_lt (self_lt_theta x)) k _)
    (finite_bound M hn k)

theorem omega_diagonal_margin (M : Model) {n : Nat} (hn : 11 ≤ n) :
    theta (value (finite M n) n) < value (omegaLift M) n := by
  simpa only [omegaLift, value] using amplified_input_lt_value (omegaLift M) hn

theorem omega_base_margin (M : Model) {n : Nat} (hn : 11 ≤ n) :
    theta (value M n) < value (omegaLift M) n := by
  simpa only [omegaLift, finite, value] using amplified_zero_lt_value (omegaLift M) hn

theorem omega_bound (M : Model) {n : Nat} (hn : 11 ≤ n) :
    iter theta (n + 1) (value M n) < value (omegaLift M) n :=
  Nat.lt_of_le_of_lt (theta_mono (finite_bound M hn n)) (omega_diagonal_margin M hn)

theorem join_base_margin (base : Model) (children : Nat → Model)
    {n : Nat} (hn : 11 ≤ n) :
    theta (value base n) < value (join base children) n := by
  simpa only [join, value] using amplified_zero_lt_value (join base children) hn

theorem ramify_margin (base : Model) (a : Tree) {n : Nat} (hn : 11 ≤ n) :
    theta (value base n) < value (ramify base a) n := by
  cases a with
  | leaf => exact omega_base_margin base hn
  | node f =>
      let children := fun i => ramify base (f i)
      have h0 := join_base_margin base children hn
      have h1 := omega_base_margin (join base children) hn
      exact Nat.lt_trans h0 (Nat.lt_trans (self_lt_theta _) h1)

theorem base_margin {n : Nat} (hn : 11 ≤ n) :
    theta (BusyLean.finalFamily n) < value baseModel n := by
  simpa only [baseModel, BusyLean.finalFamily] using amplified_zero_lt_value baseModel hn

theorem initialOmega_bound {n : Nat} (hn : 11 ≤ n) :
    iter theta (n + 2) (BusyLean.finalFamily n) < value initialOmega n := by
  have h0 := theta_iter_mono (Nat.le_of_lt (base_margin hn)) (n + 1)
  have h1 := omega_bound baseModel hn
  have h := Nat.lt_of_le_of_lt h0 h1
  rw [iter_succ_input] at h
  exact h

theorem ramified_bound {n : Nat} (hn : 11 ≤ n) :
    iter theta (n + 3) (BusyLean.finalFamily n) < value ramifiedModel n :=
  Nat.lt_of_le_of_lt (theta_mono (Nat.le_of_lt (initialOmega_bound hn)))
    (ramify_margin initialOmega selfSchedule hn)

theorem final_bound {n : Nat} (hn : 11 ≤ n) :
    iter theta (n + 4) (BusyLean.finalFamily n) < value finalModel n :=
  Nat.lt_of_le_of_lt (theta_mono (Nat.le_of_lt (ramified_bound hn)))
    (omega_base_margin ramifiedModel hn)

theorem scalar_lt_of_feedback_bound {x y : Nat}
    (h : iter theta 46 x < y) : x < y :=
  Nat.lt_of_le_of_lt
    (le_iter theta (fun z => Nat.le_of_lt (self_lt_theta z)) 46 x) h

end BusyLean7

namespace BusyLean
/-- A 46-fold tower-height feedback lower bound, not just an increment. -/
theorem contender_6_tower_lt_contender_7 :
    BusyLean7.iter BusyLean7.theta 46 contender_6 < contender_7 := by
  simpa only [contender_6, contender_7] using
    (BusyLean7.final_bound (n := 42) (by decide))

/-- Proposed strict comparison with the exact pinned current contender. -/
theorem contender_6_lt_contender_7 : contender_6 < contender_7 :=
  BusyLean7.scalar_lt_of_feedback_bound contender_6_tower_lt_contender_7
end BusyLean
