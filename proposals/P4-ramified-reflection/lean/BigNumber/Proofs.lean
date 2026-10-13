import BigNumber.Contender
import BigNumber.Baseline

/-!
Constructive proof source. This file has NOT been compiler-checked in the
preparation environment. No placeholders or user axioms are present.
Audit.lean and scripts/verify_lean.py are the required acceptance gates.
-/
namespace BigNumber
namespace Lists
universe u v

/-- An explicit inductive occurrence relation avoids extensional set machinery. -/
inductive Occ {α : Type u} (x : α) : List α → Prop where
  | head {xs : List α} : Occ x (x :: xs)
  | tail {y : α} {xs : List α} : Occ x xs → Occ x (y :: xs)

theorem occCatLeft {α : Type u} {x : α} {xs ys : List α}
    (h : Occ x xs) : Occ x (cat xs ys) := by
  induction h with
  | head => exact Occ.head
  | tail h ih => exact Occ.tail ih

theorem occCatRight {α : Type u} {x : α} (xs : List α)
    {ys : List α} (h : Occ x ys) : Occ x (cat xs ys) := by
  induction xs with
  | nil => exact h
  | cons a xs ih => exact Occ.tail ih

theorem occMap {α : Type u} {β : Type v} (f : α → β)
    {x : α} {xs : List α} (h : Occ x xs) : Occ (f x) (map f xs) := by
  induction h with
  | head => exact Occ.head
  | tail h ih => exact Occ.tail ih

theorem occFlatten {α : Type u} {x : α} {xs : List α}
    {xss : List (List α)} (hx : Occ x xs) (hs : Occ xs xss) :
    Occ x (flatten xss) := by
  induction hs with
  | head => exact occCatLeft hx
  | tail hs ih => exact occCatRight _ ih

theorem occProd {α : Type u} {β : Type v} {x : α} {y : β}
    {xs : List α} {ys : List β} (hx : Occ x xs) (hy : Occ y ys) :
    Occ (x, y) (prod xs ys) := by
  induction hx with
  | head => exact occCatLeft (occMap (fun z => (x, z)) hy)
  | tail hx ih => exact occCatRight _ ih

theorem maximum_bound {α : Type u} (f : α → Nat)
    {x : α} {xs : List α} (h : Occ x xs) : f x ≤ maximum f xs := by
  induction h with
  | head => exact Nat.le_max_left _ _
  | tail h ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem maxBy_occ {α : Type u} (f : α → Nat) (current : Nat) (best : α) :
    (xs : List α) →
    Occ (maxBy f current best xs) xs ∨ maxBy f current best xs = best
  | [] => Or.inr rfl
  | x :: xs => by
      by_cases h : current < f x
      · simp only [maxBy, if_pos h]
        cases maxBy_occ f (f x) x xs with
        | inl hx => exact Or.inl (Occ.tail hx)
        | inr heq =>
            apply Or.inl
            rw [heq]
            exact Occ.head
      · simp only [maxBy, if_neg h]
        cases maxBy_occ f current best xs with
        | inl hx => exact Or.inl (Occ.tail hx)
        | inr heq => exact Or.inr heq

end Lists

namespace Legacy
open BigNumber.Lists

theorem zero_occ (n : Nat) : Occ Tm.zero (terms (n + 1)) :=
  occFlatten Occ.head (Occ.tail (Occ.tail (Occ.tail Occ.head)))

theorem contender_5_term_occ : Occ contender_5_term (terms 42) := by
  change Occ (maxBy value 0 Tm.zero (terms 42)) (terms 42)
  cases maxBy_occ value 0 Tm.zero (terms 42) with
  | inl h => exact h
  | inr h =>
      rw [h]
      exact zero_occ 41

end Legacy

namespace Language
open BigNumber.Lists

theorem previous_occ {d : Nat} {t : Tm} (h : Occ t (terms d)) :
    Occ t (terms (d + 1)) := occFlatten h Occ.head

theorem terms_mono {a b : Nat} (hab : a ≤ b)
    {t : Tm} (h : Occ t (terms a)) : Occ t (terms b) := by
  induction hab with
  | refl => exact h
  | step hab ih => exact previous_occ ih

theorem zero_occ (d : Nat) : Occ Tm.zero (terms (d + 1)) :=
  occFlatten Occ.head (Occ.tail Occ.head)

theorem succ_occ (d : Nat) : Occ Tm.succ (terms (d + 1)) :=
  occFlatten (Occ.tail Occ.head) (Occ.tail Occ.head)

theorem oracle_occ (d : Nat) : Occ Tm.oracle (terms (d + 1)) :=
  occFlatten (Occ.tail (Occ.tail (Occ.tail (Occ.tail Occ.head))))
    (Occ.tail Occ.head)

theorem app_occ {d : Nat} {f x : Tm}
    (hf : Occ f (terms d)) (hx : Occ x (terms d)) :
    Occ (Tm.app f x) (terms (d + 1)) :=
  occFlatten (occMap (fun p => Tm.app p.1 p.2) (occProd hf hx))
    (Occ.tail (Occ.tail (Occ.tail (Occ.tail Occ.head))))

theorem quote_occ {d : Nat} {t : Legacy.Tm}
    (h : Occ t (Legacy.terms d)) : Occ (Tm.quote t) (terms (d + 1)) :=
  occFlatten (occMap Tm.quote h)
    (Occ.tail (Occ.tail (Occ.tail (Occ.tail (Occ.tail (Occ.tail (Occ.tail Occ.head)))))))

theorem numeral_occ (n : Nat) : Occ (numeral n) (terms (n + 1)) := by
  induction n with
  | zero => exact zero_occ 0
  | succ n ih => exact app_occ (succ_occ n) ih

theorem interp_numeral (q : Nat → Nat → Nat) (env : List Pack) (n : Nat) :
    interp q (numeral n) env = ⟨Ty.nat, n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (⟨Ty.nat, Nat.succ (cast Ty.nat (interp q (numeral n) env))⟩ : Pack)
        = ⟨Ty.nat, Nat.succ n⟩
      rw [ih]
      rfl

theorem value_numeral (q : Nat → Nat → Nat) (n : Nat) :
    value q (numeral n) = n := by
  unfold value
  rw [interp_numeral]

theorem oracleWitness_occ (i n : Nat) (hi : i ≤ n) :
    Occ (oracleWitness i n) (terms (n + 4)) := by
  have h1 : Occ (.app .oracle (numeral i)) (terms (i + 2)) :=
    app_occ (oracle_occ i) (numeral_occ i)
  have h2 : Occ (.app .oracle (numeral i)) (terms (n + 2)) :=
    terms_mono (Nat.add_le_add_right hi 2) h1
  have h3 : Occ (.app (.app .oracle (numeral i)) (numeral n)) (terms (n + 3)) :=
    app_occ h2 (previous_occ (numeral_occ n))
  exact app_occ (succ_occ (n + 2)) h3

theorem value_oracleWitness (q : Nat → Nat → Nat) (i n : Nat) :
    value q (oracleWitness i n) = Nat.succ (q i n) := by
  simp only [value, oracleWitness, interp, interp_numeral, cast, castPair]

theorem value_succ_quote (q : Nat → Nat → Nat) (t : Legacy.Tm) :
    value q (.app .succ (.quote t)) = Nat.succ (Legacy.value t) := rfl

theorem input_lt_envelope (q : Nat → Nat → Nat) (n : Nat) :
    n < envelope q (n + 4) := by
  have h := maximum_bound (value q)
    (previous_occ (previous_occ (numeral_occ (n + 1))))
  rw [value_numeral] at h
  exact h

/-- The numerical comparison never normalizes the old winning term. -/
theorem baseline_lt_envelope (q : Nat → Nat → Nat) :
    Legacy.contender_5 < envelope q 68 := by
  have hq : Occ (.quote Legacy.contender_5_term) (terms 43) :=
    quote_occ Legacy.contender_5_term_occ
  have hs : Occ (.app .succ (.quote Legacy.contender_5_term)) (terms 44) :=
    app_occ (succ_occ 42) hq
  have hu := terms_mono (show 44 ≤ 68 from by decide) hs
  have hb := maximum_bound (value q) hu
  rw [value_succ_quote] at hb
  exact hb

end Language

/-- An explicit pointwise, not merely asymptotic, reflection comparison. -/
theorem reflect_child_lt (f : Nat → Tree) (i n : Nat) (hi : i ≤ n) :
    reflect (f i) n < reflect (.sup f) n := by
  have h := Lists.maximum_bound (Language.value (fun j x => reflect (f j) x))
    (Language.oracleWitness_occ i n hi)
  rw [Language.value_oracleWitness] at h
  exact h

theorem input_lt_reflect (a : Tree) (n : Nat) : n < reflect a n := by
  cases a with
  | zero => exact Language.input_lt_envelope (fun _ _ => 0) n
  | sup f => exact Language.input_lt_envelope (fun i x => reflect (f i) x) n

theorem high_zero (a : Tree) (s : Tree → Tree) :
    high a s 0 = Tree.sup (fun k => iterate s k a) := rfl

theorem reflect_boost_lt (a : Tree) (n : Nat) : reflect a n < reflect (boost a) n :=
  reflect_child_lt
    (fun | 0 => a | k + 1 => high a step (reflect a (k + 64)))
    0 n (Nat.zero_le n)

theorem boost_feedback_lt (a : Tree) (n : Nat) (hn : 1 ≤ n) :
    reflect (high a step (reflect a 64)) n < reflect (boost a) n :=
  reflect_child_lt
    (fun | 0 => a | k + 1 => high a step (reflect a (k + 64)))
    1 n hn

theorem high_level_lt_grand (k n : Nat) (hk : k ≤ n) :
    reflect (high Tree.zero boost k) n < reflect grandIndex n :=
  reflect_child_lt (fun j => high Tree.zero boost j) k n hk

theorem finite_feedback_lt_grand (n j : Nat) (hj : j ≤ n) :
    reflect (iterate boost j Tree.zero) n < reflect grandIndex n := by
  have h1 := reflect_child_lt (fun k => iterate boost k Tree.zero) j n hj
  have h2 := reflect_child_lt (fun k => high Tree.zero boost k) 0 n (Nat.zero_le n)
  rw [high_zero] at h2
  exact Nat.lt_trans h1 h2

theorem contender_5_lt_reflect (a : Tree) : Legacy.contender_5 < reflect a 64 := by
  cases a with
  | zero => exact Language.baseline_lt_envelope (fun _ _ => 0)
  | sup f => exact Language.baseline_lt_envelope (fun i x => reflect (f i) x)

/-- The required strict comparison (subject to the compiler/audit gate). -/
theorem contender_5_lt_contender_6 : Legacy.contender_5 < contender_6 :=
  contender_5_lt_reflect grandIndex

end BigNumber
