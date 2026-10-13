import BusyLean.Contender65
import BusyLean.Comparison64

/-! # Contender 65: comparison theorems -/

namespace BusyLean

open Ordinal (CTree Closures)

/-- A closure pair whose number closure strictly dominates its oracle and argument. -/
def Good (c : Closures) : Prop := ∀ (g : Nat → Nat) (m : Nat), g m < c.2 g m ∧ m < c.2 g m

theorem good_num2Lift (P : List Ordinal.PTL2.Ty) (σ : Ordinal.PTL2.Env P)
    (t : (CTree → CTree) → CTree → CTree) : Good (t, Ordinal.num2Lift P σ) :=
  fun g m => ⟨Ordinal.oracle_lt_num2Lift P σ g m, Ordinal.input_lt_num2Lift P σ g m⟩

theorem good_lim (t : (CTree → CTree) → CTree → CTree) (cs : Nat → Closures)
    (h : ∀ i, Good (cs i)) :
    Good (t, fun g m => Ordinal.maxUpTo (fun i => (cs i).2 g m) m) := by
  intro g m
  have h0 := Ordinal.le_maxUpTo (fun i => (cs i).2 g m) (Nat.zero_le m)
  exact ⟨Nat.lt_of_lt_of_le (h 0 g m).1 h0, Nat.lt_of_lt_of_le (h 0 g m).2 h0⟩

theorem good_step2 (N : Nat) (g0 : Nat → Nat) (c : Closures) : Good (step2 N g0 c) :=
  good_num2Lift _ _ _

theorem good_metaS (N : Nat) (g0 : Nat → Nat) : ∀ (a : CTree) (c : Closures), Good (metaS N g0 a c) := by
  intro a
  induction a with
  | zero => intro c; exact good_step2 N g0 c
  | succ a _ => intro c; exact good_num2Lift _ _ _
  | lim f ih => intro c; exact good_lim _ _ fun i => ih i c
  | supL _ _ => intro c; exact good_step2 N g0 c
  | supH _ _ => intro c; exact good_step2 N g0 c

theorem good_towerFrom (S : Closures → Closures) (hS : ∀ c, Good (S c)) (c0 : Closures)
    (h0 : Good c0) : ∀ a : CTree, Good (towerFrom S c0 a) := by
  intro a
  induction a with
  | zero => exact h0
  | succ a _ => exact hS _
  | lim f ih => exact good_lim _ _ ih
  | supL _ _ => exact h0
  | supH _ _ => exact h0

theorem good_metaSClosure (N : Nat) (g0 : Nat → Nat) (T : CTree) :
    Good (towerFrom (metaS N g0 T) (base61 N g0) T) :=
  good_towerFrom _ (good_metaS N g0 T) _ (good_num2Lift _ _ _) T

theorem input_lt_family64 (n : Nat) : n < family64 n :=
  Nat.lt_trans (input_lt_F64 n) (input_lt_F64 (F64 n))

/-- At every input, `F65` exceeds Contender 64's family. -/
theorem family64_lt_F65 (n : Nat) : family64 n < F65 n := by
  have hS := good_metaSClosure (family64 n) family64 (metaSTree (family64 n)) family64
  have h1 := (Ordinal.le_hier (fun x => Nat.le_of_lt (hS x).2) (metaSTree (family64 n))
    (family64 n)).1
  exact Nat.lt_trans (input_lt_family64 (family64 n)) (Nat.lt_of_lt_of_le (hS (family64 n)).1 h1)

theorem input_lt_F65 (n : Nat) : n < F65 n :=
  Nat.lt_trans (input_lt_family64 n) (family64_lt_F65 n)

/-- **The required comparison**: Contender 64 is strictly smaller than Contender 65. -/
theorem contender_64_lt_contender_65 : contender_64 < contender_65 :=
  Nat.lt_trans (family64_lt_F65 42) (input_lt_F65 (F65 42))

theorem contender_63_lt_contender_65 : contender_63 < contender_65 :=
  Nat.lt_trans contender_63_lt_contender_64 contender_64_lt_contender_65

end BusyLean
